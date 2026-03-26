import ArgumentParser
import Driver
import Foundation
import FrontEnd
import Utilities

/// The top-level command of `hc`.
@main struct CommandLine: AsyncParsableCommand {

  /// Configuration for this command.
  public static let configuration = CommandConfiguration(commandName: "hc")

  /// The paths at which libraries may be found.
  @Option(
    name: [.customShort("L")],
    help: ArgumentHelp(
      "Add a directory to the library search path.",
      valueName: "path"),
    transform: URL.init(fileURLWithPath:))
  private var librarySearchPaths: [URL] = []

  /// The path containing cached module data.
  @Option(
    name: [.customLong("module-cache")],
    help: ArgumentHelp(
      "Specify the module cache path.",
      valueName: "path"),
    transform: URL.init(fileURLWithPath:))
  private var moduleCachePath: URL?

  @Option(
    name: [.customLong("target")],
    help: ArgumentHelp(
      "Specify the LLVM target triple or 'host'.",
      valueName: "triple"))
  private var targetTriple: Driver.TargetSelection = .host

  @Option(
    name: [.customLong("target-cpu")],
    help: ArgumentHelp(
      "Specify the target CPU or 'host'.",
      valueName: "cpu"))
  private var targetCPU: Driver.TargetSelection = .host

  @Option(
    name: [.customLong("target-features")],
    help: ArgumentHelp(
      "Specify the target CPU features or 'host'.",
      valueName: "features"))
  private var targetFeatures: Driver.TargetSelection = .host

  /// `true` iff the driver should not read/write modules from/to the cache.
  @Flag(help: "Disable caching.")
  private var noCaching: Bool = false

  /// `true` iff the driver should not load the standard library.
  @Flag(
    name: [.customLong("no-std")],
    help: "Do not load the standard library")
  private var noStandardLibrary: Bool = false

  /// The kind of output that should be produced by the compiler.
  @Option(
    name: [.customLong("emit")],
    help: ArgumentHelp(
      "Produce the specified output: \(OutputType.allValueStrings.joined(separator: ", ")).",
      valueName: "output-type"))
  private var outputType: OutputType = .binary

  @Option(
    name: [.customShort("o")],
    help: ArgumentHelp(
      "Write output to <file>.",
      valueName: "file"),
    transform: URL.init(fileURLWithPath:))
  private var outputURL: URL?

  /// The configuration of the tree printer.
  @Flag(help: "Tree printer configuration")
  private var treePrinterFlags: [TreePrinterFlag] = []

  /// `true` iff verbose information about compilation should be printed to the standard output.
  @Flag(
    name: [.short, .long],
    help: "Use verbose output.")
  private var verbose: Bool = false

  /// The input files and directories passed to the command.
  @Argument(transform: URL.init(fileURLWithPath:))
  private var inputs: [URL] = []

  /// Creates a new instance with default options.
  public init() {}

  /// Executes the command.
  public mutating func run() async throws {
    try configureSearchPaths()
    var driver = Driver(
      moduleCachePath: noCaching ? nil : moduleCachePath!,
      targetConfiguration: .init(targetTriple: targetTriple, cpu: targetCPU, features: targetFeatures),
      librarySearchPaths: librarySearchPaths)

    do {
      // Load the standard library.
      if !noStandardLibrary {
        note("load Hylo's standard library")
        try await driver.loadStandardLibrary()
      }

      // Create a module for the product being compiled.
      let product = productName(inputs)
      note("start compiling \(product)")
      let module = driver.program.demandModule(product)
      if !noStandardLibrary {
        driver.program[module].addDependency(Module.standardLibraryName)
      }

      // Compile from sources.
      let sources = try sourceFiles(recursivelyContainedIn: inputs)
      await perform("parsing", for: module, { await driver.parse(sources, into: module) })
      await perform("scoping", for: module, { await driver.assignScopes(of: module) })
      if outputType == .ast {
        try emitAst(module, in: driver.program, name: product)
        return
      }

      await perform("typing", for: module, { await driver.assignTypes(of: module) })
      if outputType == .typedAST {
        try emitAst(module, in: driver.program, name: product)
        return
      }

      await perform("lowering", for: module, { await driver.lower(module) })
      if outputType == .rawIR {
        try emitIR(module, in: driver.program, name: product)
        return
      }

      await perform("normalization", for: module, { await driver.applyTransformationPasses(module) })
      if outputType == .ir {
        try emitIR(module, in: driver.program, name: product)
        return
      }

      try await perform("code generation", for: module, { try await driver.lowerToLLVM(module) })
      if outputType == .llvm {
        try emitLLVM(module, from: driver, name: product)
        return
      }
      if outputType == .asm {
        try write(driver.assembly(of: module), to: asmFile(product))
        return
      }
      if outputType == .objectFiles {
        let modules = Array(driver.program.moduleIdentities)
        for dependency in modules where dependency != module {
          await perform("lowering", for: dependency, { await driver.lower(dependency) })
          await perform(
            "normalization",
            for: dependency,
            { await driver.applyTransformationPasses(dependency) })
          try await perform(
            "code generation",
            for: dependency,
            { try await driver.lowerToLLVM(dependency) })
        }
        let directory = try objectFilesDirectory()
        _ = try driver.writeObjectFiles(for: modules, into: directory)
        note("written \(directory.path)")
        return
      }

      // Write the module to the cache for future runs.
      let a = try driver.program.archive(module: module)
      note("module archive size: \(a.count)")

      assert(outputType == .binary)
      try await perform("generating executable", for: module,
        { try await driver.generateExecutable(for: module, writingTo: binaryFile(product)) })
    } catch let e as CompilationError {
      render(e.diagnostics.elements)
      CommandLine.exit(withError: ExitCode.failure)
    }

    func perform(_ phase: String, for module: FrontEnd.Module.ID,
      _ action: () async throws -> (elapsed: Duration, containsError: Bool)) async rethrows {
      let a = try await action()
      note("\(phase) completed in \(a.elapsed.human)")
      exitOnError(driver.program[module])
    }
  }

  /// Emits the AST of `module` in `program` with name `name`, using the tree printer.
  private func emitAst(
    _ module: Module.ID, in program: Program, name: Module.Name
  ) throws {
    let target = astFile(name)
    let c = treePrinterConfiguration(for: treePrinterFlags)
    let a = program.select(from: module, .satisfies({ program.parent(containing: $0).isFile }))
    let r = a.joinedString(separator: "\n") { d in program.show(d, configuration: c) }
    try write(r, to: target)
  }

  /// Emits the IR of `module` in `program` with name `name`.
  private func emitIR(
    _ module: Module.ID, in program: Program, name: Module.Name
  ) throws {
    let target = irFile(name)
    let r = program[module].functions.joinedString(separator: "\n") { f in program.show(f) }
    try write(r, to: target)
  }

  /// Emits the LLVM IR of `module` in `program` with name `name`.
  private func emitLLVM(
    _ module: Module.ID, from driver: Driver, name: Module.Name
  ) throws {
    guard let output = driver.llvmIR(of: module) else {
      fatalError("missing LLVM output")
    }
    try write(output, to: llvmFile(name))
  }

  /// Writes `content` to `url`, or to the standard output if `url` is "-".
  private func write(_ content: String, to url: URL) throws {
    if outputURL?.relativePath == "-" {
      // User wants to write to the standard output.
      print(content)
    } else {
      try content.write(to: url, atomically: true, encoding: .utf8)
      note("written \(url.path)")
    }
  }

  /// Sets up the value of search paths for locating libraries and cached artifacts.
  private mutating func configureSearchPaths() throws {
    let fm = FileManager.default
    if let m = moduleCachePath {
      librarySearchPaths.append(m)
    } else {
      let m = fm.temporaryDirectory.appending(path: ".hylocache")
      try fm.createDirectory(at: m, withIntermediateDirectories: true)
      note("using module cache path: \(m.path)")
      librarySearchPaths.append(m)
      moduleCachePath = m
    }

    librarySearchPaths = .init(librarySearchPaths.uniqued())
    librarySearchPaths.removeDuplicates()
  }

  /// Returns an array with all the source files in `inputs` and their subdirectories.
  private func sourceFiles(recursivelyContainedIn inputs: [URL]) throws -> [SourceFile] {
    var sources: [SourceFile] = []
    for url in inputs {
      if url.hasDirectoryPath {
        try SourceFile.forEach(in: url) { (f) in sources.append(f) }
      } else if url.pathExtension == "hylo" {
        try sources.append(SourceFile(contentsOf: url))
      } else {
        throw ValidationError("unexpected input: \(url.relativePath)")
      }
    }
    return sources
  }

  /// If `module` contains errors, renders all its diagnostics and exits with `ExitCode.failure`.
  /// Otherwise, does nothing.
  private func exitOnError(_ module: Module) {
    if module.containsError {
      render(module.diagnostics)
      CommandLine.exit(withError: ExitCode.failure)
    }
  }

  /// Renders the given diagnostics to the standard error.
  private func render<T: Sequence<Diagnostic>>(_ ds: T) {
    let s: Diagnostic.TextOutputStyle = ProcessInfo.ansiTerminalIsConnected ? .styled : .unstyled
    var o = ""
    for d in ds {
      d.render(into: &o, showingPaths: .absolute, style: s)
    }
    var stderr = StandardError()
    print(o, to: &stderr)
  }

  /// Writes `message` to the standard output iff `self.verbose` is `true`.
  private func note(_ message: @autoclosure () -> String) {
    if verbose {
      print(message())
    }
  }

  /// Returns the configuration corresponding to the given `flags`.
  private func treePrinterConfiguration(
    for flags: [TreePrinterFlag]
  ) -> TreePrinter.Configuration {
    .init(useVerboseTypes: flags.contains(.verboseTypes))
  }

  /// If `inputs` contains a single URL `u` whose path is non-empty, returns the last component of
  /// `u` without any path extension and stripping all leading dots. Otherwise, returns "Main".
  private func productName(_ inputs: [URL]) -> Module.Name {
    if let u = inputs.uniqueElement {
      let n = u.deletingPathExtension().lastPathComponent.drop(while: { (c) in c == "." })
      if !n.isEmpty {
        return .init(n)
      }
    }
    return "Main"
  }

  /// The type of the output files to generate.
  private enum OutputType: String, ExpressibleByArgument, CaseIterable {

    /// Abstract syntax tree before typing.
    case ast = "ast"

    /// Abstract syntax tree after typing.
    case typedAST = "typed-ast"

    /// Hylo IR before mandatory transformations.
    case rawIR = "raw-ir"

    /// Hylo IR.
    case ir = "ir"

    /// LLVM IR.
    case llvm = "llvm"

    /// Assembly.
    case asm = "asm"

    /// Object files.
    case objectFiles = "object-files"

    /// Executable binary.
    case binary = "binary"
  }

  /// Given the desired name of the compiler's product, returns the file to write when "raw-ast" is
  /// selected as the output type.
  private func astFile(_ productName: Module.Name) -> URL {
    outputURL ?? URL(fileURLWithPath: productName.description + ".ast")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "ir" or
  /// "raw-ir" is selected as the output type.
  private func irFile(_ productName: Module.Name) -> URL {
    outputURL ?? URL(fileURLWithPath: productName.description + ".ir")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "llvm" is
  /// selected as the output type.
  private func llvmFile(_ productName: Module.Name) -> URL {
    outputURL ?? URL(fileURLWithPath: productName.description + ".ll")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "asm"
  /// is selected as the output type.
  private func asmFile(_ productName: Module.Name) -> URL {
    outputURL ?? URL(fileURLWithPath: productName.description + ".s")
  }

  /// Returns the directory to write when "object-files" is selected as the output type.
  private func objectFilesDirectory() throws -> URL {
    guard outputURL?.relativePath != "-" else {
      throw ValidationError("object files cannot be written to the standard output")
    }
    return outputURL ?? URL(fileURLWithPath: "./objects")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "binary" is
  /// selected as the output type.
  private func binaryFile(_ productName: Module.Name) -> URL {
    let base = outputURL ?? URL(fileURLWithPath: productName.description)
    return base.withHostExecutableSuffix()
  }

  /// Tree printing flags.
  private enum TreePrinterFlag: String, EnumerableFlag {

    /// Prints a verbose representation of type trees.
    case verboseTypes = "print-verbose-types"

    static func name(for value: TreePrinterFlag) -> NameSpecification {
      .customLong(value.rawValue)
    }

  }

}

extension Driver.TargetSelection: ExpressibleByArgument {

  /// Creates an instance by parsing a command-line argument.
  public init(argument: String) {
    self = (argument == "host") ? .host : .specified(argument)
  }

}

extension ProcessInfo {

  /// `true` iff the terminal supports coloring.
  fileprivate static let ansiTerminalIsConnected =
    !["", "dumb", nil].contains(processInfo.environment["TERM"])

}

extension ContinuousClock.Instant.Duration {

  /// The value of `self` in nanoseconds.
  fileprivate var ns: Int64 { components.attoseconds / 1_000_000_000 }

  /// The value of `self` in microseconds.
  fileprivate var μs: Int64 { ns / 1_000 }

  /// The value of `self` in milliseconds.
  fileprivate var ms: Int64 { μs / 1_000 }

  /// A human-readable representation of `self`.
  fileprivate var human: String {
    guard abs(ns) >= 1_000 else { return "\(ns)ns" }
    guard abs(μs) >= 1_000 else { return "\(μs)μs" }
    guard abs(ms) >= 1_000 else { return "\(ms)ms" }
    return formatted()
  }

}

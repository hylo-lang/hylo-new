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
      "Produce the specified output: Possible values are: ast, typed-ast",
      valueName: "output-type"))
  private var outputType: OutputType = .typedAST

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
    var driver = Driver(moduleCachePath: noCaching ? nil : moduleCachePath!)

    // Load the standard library.
    if !noStandardLibrary {
      note("load Hylo's standard library")
      do {
        try await driver.loadStandardLibrary()
      } catch let e as CompilationError {
        render(e.diagnostics.elements)
        CommandLine.exit(withError: ExitCode.failure)
      }
    }

    // Create a module for the product being compiled.
    let product = productName(inputs)
    note("start compiling \(product)")
    let module = driver.program.demandModule(product)
    if !noStandardLibrary {
      driver.program[module].addDependency(.standardLibrary)
    }

    // Compile from sources.
    let sources = try sourceFiles(recursivelyContainedIn: inputs)
    await perform("parsing", { await driver.parse(sources, into: module) })
    await perform("scoping", { await driver.assignScopes(of: module) })
    await perform("typing", { await driver.assignTypes(of: module) })
    await perform("lowering", { await driver.lower(module) })

    let c = treePrinterConfiguration(for: treePrinterFlags)
    for d in driver.program.select(
      from: module, .satisfies({ driver.program.parent(containing: $0).isFile }))
    {
      print(driver.program.show(d, configuration: c))
    }

    let a = try driver.program.archive(module: module)
    print(a.count)

    func perform(
      _ phase: String, _ action: () async -> (elapsed: Duration, containsError: Bool)
    ) async {
      let a = await action()
      note("\(phase) completed in \(a.elapsed.human)")
      exitOnError(driver.program[module])
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

  /// Writes `message` to the standard error and exit.
  private func fatal(_ message: String) {
    var stderr = StandardError()
    print(message, to: &stderr)
    CommandLine.exit(withError: ExitCode.failure)
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
        return .init(String(n))
      }
    }
    return .init("Main")
  }

  /// The type of the output files to generate.
  private enum OutputType: String, ExpressibleByArgument {

    /// Abstract syntax tree before typing.
    case ast = "ast"

    /// Abstract syntax tree after typing.
    case typedAST = "typed-ast"

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

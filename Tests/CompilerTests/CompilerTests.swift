import Driver
import Foundation
import FrontEnd
import StandardLibrary
import Utilities
import XCTest

/// The driver for generated compiler tests.
///
/// This class is used as a driver to run the negative and positive tests. Its test cases are meant
/// to be defined in an extension that is generated either automatically as part of the build or by
/// manually invoking `hc-tests`.
final class CompilerTests: XCTestCase {

  /// Cleans up observation files from previous test runs.
  /// 
  /// This is done at most once, during the first test execution.
  private static let initialObservationCleanup: Void = {
    let root = URL(filePath: #filePath).deletingLastPathComponent()
    FileManager.default.enumerator(at: root, includingPropertiesForKeys: nil)?.forEach { url in
      if let url = url as? URL, url.pathExtension == "observed" {
        try? FileManager.default.removeItem(at: url)
      }
    }
  }()

  private struct CompilationResult {

    var driver: Driver

    let module: FrontEnd.Module.ID

    let expectations: [FileName: String]

    /// The path to the generated executable, if applicable.
    /// 
    /// The caller is responsible for removing the file after execution.
    let executable: URL?

  }

  /// The result of executing a program.
  private struct ExecutionResult {

    let standardOutput: String
    let standardError: String
    let exitCode: Int32

  }

  /// The input of a compiler test.
  struct TestDescription {

    /// The root path of the program's sources.
    let root: URL

    /// The manifest of the test.
    let manifest: Manifest

    /// What the program is expected to print to stdout when `self` is a run-stage test.
    var expectedStandardOutput: String?

    /// Creates an instance with the given properties.
    init(_ path: String) throws {
      self.root = URL(filePath: path)
      self.manifest = try Manifest(contentsOf: root)

      self.expectedStandardOutput = try? String(
        contentsOf: root.deletingPathExtension().appendingPathExtension("stdout.expected"),
        encoding: .utf8)

      if manifest.stage != .run && self.expectedStandardOutput != nil {
        throw TestFailure.invalidTestDescription("stdout assertion requires stage:run")
      }
    }

    /// `true` iff `self` describes a package.
    var isPackage: Bool {
      root.pathExtension == "package"
    }

    /// Calls `action` on each Hylo source URL in the program described by `self`.
    func forEachSourceURL(_ action: (URL) throws -> Void) throws {
      if isPackage {
        try SourceFile.forEachURL(in: root, action)
      } else {
        try action(root)
      }
    }

  }

  /// A temporary folder for caching compilation artifacts during testing.
  ///
  /// An new directory is generated every time this property is initialized and removed once all
  /// tests have run.
  private static let moduleCachePath: (url: URL, delete: @Sendable () -> Void) = {
    let m = FileManager.default
    let u = try! m.url(
      for: .itemReplacementDirectory,
      in: .userDomainMask,
      appropriateFor: m.currentDirectoryURL,
      create: true)
    return (u, { try? FileManager.default.removeItem(at: u) })
  }()

  /// Deletes cached compilation artifacts.
  override class func tearDown() {
    moduleCachePath.delete()
  }

  /// Compiles `input` expecting no compilation error, potentially executing the program.
  ///
  /// Run-stage tests execute the program, verifying the exit code and optionally the standard output.
  func testCaseRoot(_ input: TestDescription) async throws {
    _ = CompilerTests.initialObservationCleanup
    
    do {
      let result = try await compile(input)
      defer { 
        if let e = result.executable { 
          try? FileManager.default.removeItem(at: e) 
        }
      }

      try assertSansError(result.driver.program)

      guard input.manifest.stage == .run else { return }

      guard let executable = result.driver.executableURL(of: result.module) else {
        XCTFail("missing executable output")
        throw TestFailure.missingExecutableOutput
      }
      let execution: CompilerTests.ExecutionResult = try execute(executable)
      try execution.standardOutput.write(to: input.root.deletingPathExtension().appendingPathExtension("stdout.observed"), atomically: true, encoding: .utf8)

      assertExitCode(input.manifest.assertedExitCode ?? 0, in: execution, testCaseRoot: input.root)
      if let expected = input.expectedStandardOutput {
        assertStandardOutput(expected, in: execution, testCaseRoot: input.root)
      }
    } catch let error as TestFailure {
      XCTFail(error.localizedDescription + "\nSource: \(input.root.path)\n")
    } 
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: TestDescription) async throws {
    _ = CompilerTests.initialObservationCleanup

    let result = try await compile(input)
    let program = result.driver.program
    XCTAssert(program.containsError, "program compiled but an error was expected.\nSource: \(input.root.path)\n")
    assertExpectations(result.expectations, program.diagnostics)

  }
  /// Compiles `input` into `outputDirectory` and returns expected diagnostics for each compiled source file.
  private func compile(_ input: TestDescription) async throws -> CompilationResult {
    var driver = Driver(
      moduleCachePath: CompilerTests.moduleCachePath.url,
      targetConfiguration: .init(),
      standardLibrary: input.manifest.standardLibrary)

    if input.manifest.requiresStandardLibrary {
      try await driver.loadStandardLibrary()
    }

    let m = driver.program.demandModule(.init("Test"))
    if input.manifest.requiresStandardLibrary {
      driver.program[m].addDependency(Module.standardLibraryName)
    }

    var expectedDiagnostics: [FileName: String] = [:]
    try input.forEachSourceURL { (u) in
      let source = try SourceFile(contentsOf: u)
      driver.program[m].addSource(source)

      let v = u.deletingPathExtension().appendingPathExtension("diagnostics.expected")
      let expected = try? String(contentsOf: v, encoding: .utf8)
      expectedDiagnostics[source.name] = expected
    }

    var executable: URL? = nil

    func done() -> CompilationResult {
      .init(
        driver: driver,
        module: m,
        expectations: expectedDiagnostics,
        executable: executable)
    }

    // Exit if there are parsing errors or if the stage is set to `parsing`.
    if driver.program[m].containsError || (input.manifest.stage == .parsing) { return done() }

    // Semantic analysis.
    if await driver.assignScopes(of: m).containsError { return done() }
    if await driver.assignTypes(of: m).containsError { return done() }
    if input.manifest.stage == .typing { return done() }

    // IR Lowering.
    if await driver.lower(m).containsError { return done() }
    try saveObservedIR(of: m, in: driver.program, extension: "lowered-ir.observed")
    if await driver.applyTransformationPasses(m).containsError { return done() }
    try saveObservedIR(of: m, in: driver.program, extension: "transformed-ir.observed")
    if input.manifest.stage == .lowering { return done() }

    // LLVM Lowering.
    if (try driver.lowerToLLVM(m)).containsError { return done() }
    try saveLLVM(llCode: driver.llvmIR(of: m)!, contextRoot: input.root)
    if input.manifest.stage == .llvmLowering { return done() }

    // When the stdlib can be compiled, lower it to LLVM so generateExecutable can link it.
    if input.manifest.requiresStandardLibrary {
      // let stdlibID = driver.program.demandModule(Module.standardLibraryName)
      // if await driver.lower(stdlibID).containsError { return done() }
      // if await driver.applyTransformationPasses(stdlibID).containsError { return done() }
      // if (try driver.lowerToLLVM(stdlibID)).containsError { return done() }
    }

    if input.manifest.stage == .executableLinking || input.manifest.stage == .run {
      let outputDirectory = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
      try FileManager.default.createDirectory(at: outputDirectory, withIntermediateDirectories: false)

      executable = outputDirectory.appendingPathComponent(driver.program[m].name)
      _ = try driver.generateExecutable(for: m, writingTo: executable)
    }

    return done()
  }

  /// Saves the IR of module `m` for each of its source files separately.
  ///
  /// The outputs are written in the same directory as the source files, with the same name but
  /// with the extension changed to `extension`.
  private func saveObservedIR(of m: Module.ID, in program: Program, extension: String) throws {
    /// The IR functions corresponding to a given source file at url.
    var sourceToIr: [URL : String] = [:]

    var printer = TreePrinter(program: program)

    for f in program[m].functions {
      // FIXME: use mangled name instead of this possibly incomplete hack.
      let d = switch(f.name) {
        case .lowered(let d): d
        case .synthesized(let d, _): d
        case .initializer(let d): DeclarationIdentity(d)
        case .existentialized(let n): 
          switch n {
          case .lowered(let d): d
          case .synthesized(let d, _): d
          case .initializer(let d): DeclarationIdentity(d)
          case .existentialized(_): fatalError("nested existentialized function")
          }
      }

      guard case .local(let url) = program[d].site.source.name else { continue }

      sourceToIr[url, default: ""] += printer.show(f) + "\n"
    }

    for (file, ir) in sourceToIr {
      let o = file.deletingPathExtension().appendingPathExtension(`extension`)
      try ir.write(to: o, atomically: false, encoding: .utf8)
    }
  }

  /// Saves the LLVM code to a file in the test directory.
  private func saveLLVM(llCode: String, contextRoot: URL) throws {
    let o = contextRoot.deletingPathExtension().appendingPathExtension("ll.observed")
    try llCode.write(to: o, atomically: false, encoding: .utf8)
  }

  /// Asserts that the exit code of `observed` matches `expected`.
  private func assertExitCode(_ expected: Int32, in observed: ExecutionResult, testCaseRoot: URL) {
    XCTAssertEqual(
      observed.exitCode,
      expected,
      "mismatched exit code.\nstdout:\n\(observed.standardOutput)\nstderr:\n\(observed.standardError)\nSource: \(testCaseRoot.path)\n")
  }

  /// Asserts that the standard output of `observed` matches `expected`.
  private func assertStandardOutput(_ expected: String, in observed: ExecutionResult, testCaseRoot: URL) {
    XCTAssertEqual(
      observed.standardOutput,
      expected,
      "mismatched stdout.\nSource: \(testCaseRoot.path)\n")
  }

  private func execute(_ executable: URL) throws -> ExecutionResult {
    let process = Process()
    let standardOutput = Pipe()
    let standardError = Pipe()
    process.executableURL = executable
    process.standardOutput = standardOutput
    process.standardError = standardError
    try process.run()
    process.waitUntilExit()

    let stdout = String(decoding: standardOutput.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)
    let stderr = String(decoding: standardError.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self)

    return .init(
      standardOutput: stdout,
      standardError: stderr,
      exitCode: process.terminationStatus)
  }

  /// An error thrown to signal test failure with given reason.
  private enum TestFailure: Error {
    case missingExecutableOutput
    case compilationError(String)
    case invalidTestDescription(String)

    var localizedDescription: String {
      switch self {
      case .missingExecutableOutput:
        return "missing executable output"
      case .compilationError(let message):
        return "Compilation failure:\n\(message)"
      case .invalidTestDescription(let d):
        return "Invalid test description (\(d))"
      }
    }
  }

  /// Asserts that the expected `diagnostics` of each source file in `expectations` match those
  /// obtained during compilation.
  private func assertExpectations<T: Collection<Diagnostic>>(
    _ expectations: [FileName: String], _ diagnostics: T
  ) {
    if expectations.isEmpty { return }

    let root = URL(filePath: #filePath).deletingLastPathComponent()
    let observations: [FileName: [Diagnostic]] = .init(
      grouping: diagnostics, by: \.site.source.name)

    var report = ""
    for (n, e) in expectations {
      var o = ""
      for d in observations[n, default: []].sorted() {
        d.render(into: &o, showingPaths: .relative(to: root), style: .unstyled)
      }

      let lhs = e.split(whereSeparator: \.isNewline)
      let rhs = o.split(whereSeparator: \.isNewline)
      let delta = lhs.difference(from: rhs).inferringMoves()

      if !delta.isEmpty {
        report.write(Self.explain(difference: delta, relativeTo: lhs, named: n))

        guard case .local(let u) = n else { continue }
        let v = u.deletingPathExtension().appendingPathExtension("observed")
        try? o.write(to: v, atomically: true, encoding: .utf8)
      }
    }

    if !report.isEmpty {
      XCTFail("observed output does match expecation:" + report)
    }
  }

  /// Asserts that `program` does not contain any error.
  private func assertSansError(_ program: Program) throws {
    if !program.containsError { return }

    let root = URL(filePath: #filePath).deletingLastPathComponent()
    let observations: [FileName: [Diagnostic]] = .init(
      grouping: program.diagnostics, by: \.site.source.name)

    var report = "program contains one or more errors:\n"
    for (n, e) in observations.sorted(by: { (a, b) in a.key.lexicographicallyPrecedes(b.key) }) {
      var o = ""
      for d in e.sorted() {
        d.render(into: &o, showingPaths: .relative(to: root), style: .unstyled)
        if case .local(let u) = n {
          let v = u.deletingPathExtension().appendingPathExtension("diagnostics.observed")
          try? o.write(to: v, atomically: true, encoding: .utf8)
        }
      }
      report.write(o)
    }
    throw TestFailure.compilationError(report)
  }

  /// Returns a message explaining `delta`, which is the result of comparing `expectation` to some
  /// observed result.
  private static func explain(
    difference delta: CollectionDifference<String.SubSequence>,
    relativeTo expectation: [Substring], named name: FileName
  ) -> String {
    var patch: [[(Character, Substring)]] = []

    for change in delta {
      switch change {
      case .insert(let i, let line, _):
        while patch.count <= i { patch.append([]) }
        patch[i].append(("+", line))
      case .remove(let i, let line, _):
        while patch.count <= i { patch.append([]) }
        patch[i].append(("-", line))
      }
    }

    var report = "\n> \(name)"

    for i in patch.indices {
      if patch[i].isEmpty && (i < expectation.count) {
        report.write("\n \(expectation[i])")
      } else {
        for (m, line) in patch[i] { report.write("\n\(m)\(line)") }
      }
    }

    return report
  }

}

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

  private struct CompilationResult {

    var driver: Driver

    let module: FrontEnd.Module.ID

    let expectations: [FileName: String]

    let expectedStandardOutput: String?

    /// The path to the generated executable, if applicable.
    let executable: URL?

  }

  private struct ExecutionResult {

    let standardOutput: String

    let standardError: String

    let terminationStatus: Int32

  }

  /// The input of a compiler test.
  struct TestDescription {

    /// The root path of the program's sources.
    let root: URL

    /// The manifest of the test.
    let manifest: Manifest

    /// Creates an instance with the given properties.
    init(_ path: String) throws {
      self.root = URL(filePath: path)
      self.manifest = try Manifest(contentsOf: root)
    }

    /// `true` iff `self` describes a package.
    var isPackage: Bool {
      root.pathExtension == "package"
    }

    var expectedStandardOutput: String? {
      guard !isPackage else { return nil }
      let path = root.deletingPathExtension().appendingPathExtension("stdout.expected")
      return try? String(contentsOf: path, encoding: .utf8)
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

  /// Compiles `input` expecting no compilation error.
  func positive(_ input: TestDescription) async throws {
    if input.manifest.assertedExitCode != nil, input.manifest.stage != .run {
      XCTFail("assert-exit-code requires stage:run")
      return
    }
    if input.expectedStandardOutput != nil, input.manifest.stage != .run {
      XCTFail("stdout assertion requires stage:run")
      return
    }


    do {
    try await FileManager.default.withUniqueTemporaryDirectory{ d in
      let result = try await compile(input, outputDirectory: d)
      try assertSansError(result.driver.program)

      guard input.manifest.stage == .run else { return }

      let r: CompilerTests.ExecutionResult = try execute(result)
      assertExitCode(input.manifest.assertedExitCode ?? 0, in: r)
      if let standardOutput = result.expectedStandardOutput {
        assertStandardOutput(standardOutput, in: r)
      }
    }
    } catch let error as TestFailure {
      XCTFail(error.localizedDescription)
    }
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: TestDescription) async throws {
    try await FileManager.default.withUniqueTemporaryDirectory{ d in
      let result = try await compile(input, outputDirectory: d)
      let program = result.driver.program
      XCTAssert(program.containsError, "program compiled but an error was expected")
      assertExpectations(result.expectations, program.diagnostics)
    }
  }
  /// Compiles `input` into `outputDirectory` and returns expected diagnostics for each compiled source file.
  private func compile(_ input: TestDescription, outputDirectory: URL) async throws -> CompilationResult {
    var driver = Driver(
      moduleCachePath: CompilerTests.moduleCachePath.url,
      targetConfiguration: .init(),
      standardLibrary: input.manifest.standardLibrary)

    if input.manifest.requiresStandardLibrary {
      try await driver.load(Module.standardLibraryName, withSourcesAt: localStandardLibrarySources)
    }

    let m = driver.program.demandModule(.init("Test"))
    if input.manifest.requiresStandardLibrary {
      driver.program[m].addDependency(Module.standardLibraryName)
    }

    var expectations: [FileName: String] = [:]
    try input.forEachSourceURL { (u) in
      let source = try SourceFile(contentsOf: u)
      driver.program[m].addSource(source)

      let v = u.deletingPathExtension().appendingPathExtension("expected")
      let expected = try? String(contentsOf: v, encoding: .utf8)
      expectations[source.name] = expected
    }

    var executable: URL? = nil

    func done() -> CompilationResult {
      .init(
        driver: driver,
        module: m,
        expectations: expectations,
        expectedStandardOutput: input.expectedStandardOutput,
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

    // Code generation.
    if (try await driver.lowerToLLVM(m)).containsError { return done() }
    if input.manifest.stage == .codegen { return done() }

    // When the stdlib can be compiled, lower it to LLVM so generateExecutable can link it.
    if input.manifest.requiresStandardLibrary {
      // let stdlibID = driver.program.demandModule(.standardLibrary)
      // if await driver.lower(stdlibID).containsError { return done() }
      // if await driver.applyTransformationPasses(stdlibID).containsError { return done() }
      // if (try await driver.lowerToLLVM(stdlibID)).containsError { return done() }
    }

    if input.manifest.stage == .binary || input.manifest.stage == .run {
      executable = outputDirectory.appendingPathComponent(driver.program[m].name)
      _ = try await driver.generateExecutable(for: m, writingTo: executable)
    }

    return done()
  }

  private func saveObservedIR(of m: Module.ID, in program: Program, extension: String) throws {
    /// The IR functions corresponding to a given source file at url.
    var sourceToIr: [URL : String] = [:]

    var printer = TreePrinter(program: program)

    for f in program[m].functions {
      let d = switch(f.name) {
        case .lowered(let d): d
        case .synthesized(let d, _): d
      }

      guard case .local(let url) = program[d].site.source.name else { continue }

      sourceToIr[url, default: ""] += printer.show(f) + "\n"
    }

    for (file, ir) in sourceToIr {
      let o = file.appendingPathExtension(`extension`)
      try ir.write(to: o, atomically: false, encoding: .utf8)
    }
  }

  private func execute(_ result: CompilationResult) throws -> ExecutionResult {
    guard let executable = result.driver.executableURL(of: result.module) else {
      XCTFail("missing executable output")
      throw TestFailure.missingExecutableOutput
    }

    return try execute(executable)
  }

  private func assertExitCode(_ expected: Int32, in observed: ExecutionResult) {
    XCTAssertEqual(
      observed.terminationStatus,
      expected,
      "mismatched exit code.\nstdout:\n\(observed.standardOutput)\nstderr:\n\(observed.standardError)")
  }

  private func assertStandardOutput(_ expected: String, in observed: ExecutionResult) {
    XCTAssertEqual(
      observed.standardOutput,
      expected,
      "mismatched stdout.")
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

    return .init(
      standardOutput: String(
        decoding: standardOutput.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self),
      standardError: String(
        decoding: standardError.fileHandleForReading.readDataToEndOfFile(), as: UTF8.self),
      terminationStatus: process.terminationStatus)
  }

  private enum TestFailure: Error {
    case missingExecutableOutput
    case compilationError(String)

    var localizedDescription: String {
      switch self {
      case .missingExecutableOutput:
        return "missing executable output"
      case .compilationError(let message):
        return "Compilation failure:\n\(message)"
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
          let v = u.deletingPathExtension().appendingPathExtension("observed")
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

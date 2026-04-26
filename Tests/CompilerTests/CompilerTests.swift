import Driver
import Foundation
import FrontEnd
import StandardLibrary
import Utilities
import XCTest
typealias Host = Utilities.Host

/// The driver for generated compiler tests.
///
/// This class is used as a driver to run the negative and positive tests. Its test cases are meant
/// to be defined in an extension that is generated either automatically as part of the build or by
/// manually invoking `hc-tests`.
final class CompilerTests: XCTestCase {

  /// Iff true, intermediate compilation artifacts are saved even if test cases pass.
  let alwaysSaveArtifacts = false

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
        throw TestFailure.invalidTestDescription(message: "stdout assertion requires stage:run")
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

    /// Returns where to save test-case level observations with `tag`.
    ///
    /// Package-based tests save observations at "<package-root>/<tag>.observed" while
    /// single-file tests save observations at "<source-file>.<tag>.observed".
    ///
    /// - Requires: `tag` is a valid file name on all supported operating systems.
    func testCaseLevelObservationDestination(tag: String) throws -> URL {
      if isPackage {
        root.appending(component: ".\(tag).observed")
      } else {
        root.deletingPathExtension().appendingPathExtension("\(tag).observed")
      }
    }

    /// Returns where to save the generated executable upon failure.
    func executableDestination() -> URL {
      if isPackage {
        root.appending(component: ".executable\(Host.nativeExecutableSuffix)")
      } else {
        root.deletingPathExtension().appendingPathExtension("executable\(Host.nativeExecutableSuffix)")
      }
    }

    /// Saves `contents` into a file at its test-case level observation destination
    /// as specified by `testCaseLevelObservationDestination(tag:)`.
    ///
    /// - Requires: `tag` is a valid file name on all supported operating systems.
    func saveTestCaseLevelObservation(_ contents: String, tag: String) throws {
      try contents.write(to: testCaseLevelObservationDestination(tag: tag), atomically: true, encoding: .utf8)
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

  /// The intermediate artifacts of a module's compilation.
  ///
  /// Members shall be set after the corresponding stage is completed.
  private struct Artifacts {

    /// The lowered IR of the compiled module, if any.
    var rawIR: String?

    /// The transformed IR of the compiled module, if any.
    var transformedIR: String?

    /// The compiled IR artifact of the tested module, if any.
    var llvmIR: String?

    /// The URL of the generated executable residing in a temporary directory, if any.
    ///
    /// Copied to the test case destination upon test case failure.
    var executable: URL?

    /// Saves the artifacts into test-case-level observation files of `test`.
    func save(into test: TestDescription) throws {
      if let rawIR {
        try test.saveTestCaseLevelObservation(rawIR, tag: "raw-ir")
      }
      if let transformedIR {
        try test.saveTestCaseLevelObservation(transformedIR, tag: "transformed-ir")
      }
      if let llvmIR {
        try test.saveTestCaseLevelObservation(llvmIR, tag: "ll")
      }
      if let executable {
        try FileManager.default.copyItem(at: executable, to: test.executableDestination())
      }
    }

  }

  /// Whether the test case has recorded any failures or uncaught exceptions.
  var testFailed: Bool {
    if let testRun, testRun.totalFailureCount > 0 { true } else { false }
  }

  /// The test case currently being run.
  private var testCase: TestDescription? = nil

  /// The intermediate compilation artifacts.
  private var artifacts: Artifacts = .init()

  /// Saves any available compilation artifacts on test failure
  /// or if `alwaysSaveArtifacts` is true to facilitate diagnosis.
  func saveArtifactsIfNeeded() throws {
    if testFailed || alwaysSaveArtifacts, let testCase {
      try artifacts.save(into: testCase)
    }
  }

  /// Run by XCTest after each test case.
  override func tearDownWithError() throws {
    try saveArtifactsIfNeeded()
  }

  /// The result of a successful compilation.
  private struct CompilationResult {

    /// The driver used to compile the test program.
    var driver: Driver

    /// The main module being compiled.
    let module: FrontEnd.Module.ID

    /// The expected diagnostics for each source file.
    let expectedDiagnostics: [FileName: String]

  }

  /// Compiles `input` expecting no compilation error.
  func positive(_ input: TestDescription) async throws {
    do {
      let r = try await compile(input)
      try assertSansError(r.driver.program)

      guard input.manifest.stage == .run else { return }

      guard let executable = artifacts.executable else {
        XCTFail("missing executable output")
        throw TestFailure.missingExecutableOutput
      }
      let execution = try Process.executionResult(executable)
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
    do {
      let r = try await compile(input)
      XCTAssert(r.driver.program.containsError, "program compiled but an error was expected.\nSource: \(input.root.path)\n")
      assertExpectations(r.expectedDiagnostics, r.driver.program.diagnostics)
    } catch let error as TestFailure {
      XCTFail(error.localizedDescription + "\nSource: \(input.root.path)\n")
    }
  }

  /// Compiles `input` into `outputDirectory` and returns expected diagnostics for each compiled source file.
  ///
  /// Sets up the `testCase` context and populates `artifacts` as soon as compilation stages succeed.
  private func compile(_ input: TestDescription) async throws -> CompilationResult {
    self.testCase = input

    var driver = try Driver(moduleCachePath: CompilerTests.moduleCachePath.url, targetSpecification: .native(), standardLibrary: input.manifest.standardLibrary)

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

    func done() -> CompilationResult {
      .init(
        driver: driver,
        module: m,
        expectedDiagnostics: expectedDiagnostics)
    }

    // Exit if there are parsing errors or if the stage is set to `parsing`.
    if driver.program[m].containsError || (input.manifest.stage == .parsing) { return done() }

    // Semantic analysis.
    if await driver.assignScopes(of: m).containsError { return done() }
    if await driver.assignTypes(of: m).containsError { return done() }
    if input.manifest.stage == .typing { return done() }

    // IR Lowering.
    let l = await driver.lower(m)
    if l.containsError { return done() }
    artifacts.rawIR = driver.program.show(driver.program[m].ir)

    // IR Transformation passes.
    let t = await driver.applyTransformationPasses(m)
    if t.containsError { return done() }
    artifacts.transformedIR = driver.program.show(driver.program[m].ir)

    if input.manifest.stage == .lowering { return done() }

    // LLVM Lowering.
    if (try driver.lowerToLLVM(m)).containsError { return done() }
    artifacts.llvmIR = driver.llvmIR(of: m)!
    if input.manifest.stage == .llvmLowering { return done() }

    // When the stdlib can be compiled, lower it to LLVM so generateExecutable can link it.
    if input.manifest.requiresStandardLibrary {
      // let stdlibID = driver.program.demandModule(Module.standardLibraryName)
      // if await driver.lower(stdlibID).containsError { return done() }
      // if await driver.applyTransformationPasses(stdlibID).containsError { return done() }
      // if (try driver.lowerToLLVM(stdlibID)).containsError { return done() }
    }

    if input.manifest.stage == .executableLinking || input.manifest.stage == .run {
      let outputDirectory = try FileManager.default.createUniqueTemporaryDirectory()

      let executable = outputDirectory.appendingPathComponent(driver.program[m].name)
      _ = try driver.generateExecutable(from: m, writingTo: executable)
      artifacts.executable = executable
    }

    return done()
  }

  /// Asserts that the exit code of `observed` matches `expected`.
  private func assertExitCode(_ expected: Int32, in observed: Process.ExecutionResult, testCaseRoot: URL) {
    XCTAssertEqual(
      observed.exitCode,
      expected,
      "mismatched exit code.\nstdout:\n\(observed.standardOutput)\nstderr:\n\(observed.standardError)\nSource: \(testCaseRoot.path)\n")
  }

  /// Asserts that the standard output of `observed` matches `expected`.
  private func assertStandardOutput(_ expected: String, in observed: Process.ExecutionResult, testCaseRoot: URL) {
    XCTAssertEqual(
      observed.standardOutput,
      expected,
      "mismatched stdout.\nSource: \(testCaseRoot.path)\n")
  }

  private func execute(_ executable: URL) throws -> Process.ExecutionResult {
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

    case compilationError(message: String)

    case invalidTestDescription(message: String)

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
        let v = u.deletingPathExtension().appendingPathExtension("diagnostics.observed")
        try? o.write(to: v, atomically: true, encoding: .utf8)
      }
    }

    if !report.isEmpty {
      XCTFail("observed output does match expectation:" + report)
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
    throw TestFailure.compilationError(message:report)
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

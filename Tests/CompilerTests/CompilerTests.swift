import Driver
import Foundation
import FrontEnd
import StandardLibrary
import Utilities
import XCTest

/// `true` iff intermediate compilation artifacts must be saved for successful tests.
private let artifactsAreSavedOnSuccess: Bool = false

/// The driver for generated compiler tests.
///
/// This class is used as a driver to run the negative and positive tests. Its test cases are meant
/// to be defined in an extension that is generated either automatically as part of the build or by
/// manually invoking `hc-tests`.
final class CompilerTests: XCTestCase {

  private typealias Host = Utilities.Host

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

    /// Calls `action` on each Hylo source URL in the program described by `self`.
    func forEachSourceURL(_ action: (URL) throws -> Void) throws {
      if isPackage {
        try SourceFile.forEachURL(in: root, action)
      } else {
        try action(root)
      }
    }

    /// Returns the location where save test-case level observations with `tag` are written.
    ///
    /// Package-based tests save observations at "<package-root>/<tag>.observed" while single-file
    /// tests save observations at "<source-file>.<tag>.observed".
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
      let suffix = Host.nativeExecutableSuffix
      if isPackage {
        return root.appending(component: ".executable\(suffix)")
      } else {
        return root.deletingPathExtension().appendingPathExtension("executable\(suffix)")
      }
    }

    /// Writes `contents` to the location returned by `testCaseLevelObservationDestination(tag:)`.
    ///
    /// - Requires: `tag` is a valid file name on all supported operating systems.
    func saveTestCaseLevelObservation(_ contents: String, tag: String) throws {
      let destination = try testCaseLevelObservationDestination(tag: tag)
      try contents.write(to: destination, atomically: true, encoding: .utf8)
    }

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
    /// The executable is copied to the test case destination if the compiler could produce one but
    /// the test failed.
    var executable: URL?

    /// Saves the artifacts into test-case-level observation files of `test`.
    func save(into test: TestDescription) throws {
      if let a = rawIR {
        try test.saveTestCaseLevelObservation(a, tag: "raw-ir")
      }
      if let a = transformedIR {
        try test.saveTestCaseLevelObservation(a, tag: "transformed-ir")
      }
      if let a = llvmIR {
        try test.saveTestCaseLevelObservation(a, tag: "ll")
      }
      if let a = executable {
        try FileManager.default.copyItem(at: a, to: test.executableDestination())
      }
    }

  }

  /// The result of a successful compilation.
  private struct CompilationResult {

    /// The test case that has been executed.
    let testCase: TestDescription

    /// The driver used to compile the test program.
    let driver: Driver

    /// The main module being compiled.
    let module: FrontEnd.Module.ID

    /// The expected diagnostics for each source file.
    let expectedDiagnostics: [FileName: String]

    /// The intermediate compilation artifacts.
    let artifacts: Artifacts

  }

  /// An error thrown to signal test failure with given reason.
  private enum TestFailure: Error, CustomStringConvertible {

    /// The test failed because an executable could not be located.
    case missingExecutableOutput

    /// The test failed because of a compilation error.
    case compilationError(String)

    /// The test failed because its description was invalid.
    case invalidTestDescription(String)

    /// A textual description of the error.
    var description: String {
      switch self {
      case .missingExecutableOutput:
        return "missing executable output"
      case .compilationError(let m):
        return "compilation failure: \(m)"
      case .invalidTestDescription(let m):
        return "invalid test description: \(m)"
      }
    }

  }

  /// A temporary folder for caching compilation artifacts during testing.
  ///
  /// An new directory is generated every time this property is initialized and removed once all
  /// tests have run.
  private static let moduleCachePath = Driver.temporaryModuleCachePath()

  /// `true` iff the test case has recorded a failure or an uncaught exception.
  private var testFailed: Bool {
    (testRun?.totalFailureCount ?? 0) > 0
  }

  /// Deletes cached compilation artifacts.
  override class func tearDown() {
    moduleCachePath.delete()
  }

  /// Compiles `input` expecting no compilation error.
  func positive(_ input: TestDescription) async throws {
    do {
      // Compile the input up until the specified stage.
      let r = try await compile(input)
      try assertSansError(r.driver.program)

      // Should an executable be tested?
      if input.manifest.stage == .execution {
        let e = try XCTUnwrap(r.artifacts.executable)
        let x = try Process.execute(e)
        assertExitStatus(x, describedBy: input)
      }
    } catch let error as TestFailure {
      XCTFail("\(error)\nSource: \(input.root.path)\n")
    }
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: TestDescription) async throws {
    do {
      let r = try await compile(input)
      let m = "program compiled but an error was expected.\nSource: \(input.root.path)\n"
      XCTAssert(r.driver.program.containsError, m)
      assertExpectations(r.expectedDiagnostics, r.driver.program.diagnostics)
    } catch let error as TestFailure {
      XCTFail("\(error)\nSource: \(input.root.path)\n")
    }
  }

  /// Compiles `input` and returns the resulting artifacts.
  private func compile(_ input: TestDescription) async throws -> CompilationResult {
    var driver = try Driver(
      moduleCachePath: CompilerTests.moduleCachePath.url, targetSpecification: .native())

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

    var artifacts = Artifacts()
    do {
      try await compile(
        m, until: input.manifest.stage, using: &driver,
        accumulatingArtifactsInto: &artifacts)
    } catch let e {
      try artifacts.save(into: input)
      throw e
    }

    if artifactsAreSavedOnSuccess { try artifacts.save(into: input) }
    return .init(
      testCase: input,
      driver: driver,
      module: m,
      expectedDiagnostics: expectedDiagnostics,
      artifacts: artifacts)
  }

  /// Compiles `m`, which is a module whose source have been parsed with `driver`, until `stage`,
  /// adding compilation artifacts to `artifacts`.
  private func compile(
    _ m: Module.ID, until stage: Manifest.Stage, using driver: inout Driver,
    accumulatingArtifactsInto artifacts: inout Artifacts
  ) async throws {
    // Exit if there are parsing errors or if the stage is set to `parsing`.
    if driver.program[m].containsError || (stage == .parsing) { return }

    // Semantic analysis.
    if await driver.assignScopes(of: m).containsError { return }
    if await driver.assignTypes(of: m).containsError { return }
    if stage == .typing { return }

    // IR Lowering.
    let l = await driver.lower(m)
    if l.containsError { return }
    artifacts.rawIR = driver.program.show(driver.program[m].ir)

    // IR Transformation passes.
    let t = await driver.applyTransformationPasses(m)
    if t.containsError { return }
    artifacts.transformedIR = driver.program.show(driver.program[m].ir)
    if stage == .lowering { return }

    // LLVM Lowering.
    if (try driver.compileToLLVM(m)).containsError { return }
    artifacts.llvmIR = driver.llvmIR(of: m)!
    if stage == .llvm { return }

    // When the stdlib can be compiled, lower it to LLVM so generateExecutable can link it.
    // let stdlibID = driver.program.demandModule(Module.standardLibraryName)
    // if await driver.lower(stdlibID).containsError { return done() }
    // if await driver.applyTransformationPasses(stdlibID).containsError { return done() }
    // if (try driver.lowerToLLVM(stdlibID)).containsError { return done() }

    if stage == .execution {
      let outputDirectory = try FileManager.default.createUniqueTemporaryDirectory()
      let executable = outputDirectory.appendingPathComponent(driver.program[m].name)
      _ = try driver.generateExecutable(from: m, writingTo: executable)
      artifacts.executable = executable
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
    throw TestFailure.compilationError(report)
  }

  /// Asserts that the exit code of `observed` matches the one described by `input`.
  private func assertExitStatus(
    _ observed: Process.ExecutionReport, describedBy input: TestDescription
  ) {
    XCTAssertEqual(
      observed.exitCode, input.manifest.exitStatus,
      "mismatched exit code.\n\(observed.details(reportingAt: input.root))")
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

extension Process.ExecutionReport {

  /// Returns a description of `self`, which is the result of running `testCase`.
  fileprivate func details(reportingAt testCase: URL) -> String {
    """
    source: \(testCase.path)
    status: \(exitCode) (\(terminationReason))

    stdout:
    \(standardOutput)

    stderr:
    \(standardError)
    """
  }

}

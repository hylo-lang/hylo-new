import Driver
import Foundation
import FrontEnd
import StandardLibrary
import Utilities
import StableCollections
import XCTest

/// `true` iff intermediate compilation artifacts shall be saved for successful tests.
private let alwaysSaveArtifacts: Bool = false

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
      let tag = ArtifactTag.executable
      if isPackage {
        return root.appending(component: ".\(tag).observed\(suffix)")
      } else {
        return root.deletingPathExtension().appendingPathExtension("\(tag).observed\(suffix)")
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

  /// The type of a compilation artifact.
  enum ArtifactTag: String, CustomStringConvertible, Comparable {

    /// Hylo IR immediately after lowering, without any processing.
    case rawIR = "raw-ir"

    /// Hylo IR after mandatory transformation passes.
    case refinedIR = "refined-ir"

    /// LLVM IR.
    case llvmIR = "llvm-ir"

    /// The executable generated from the compiled program.
    case executable = "executable"

    /// All textual artifacts of the compilation and testing pipeline.
    static var allTextual: [ArtifactTag] {
      [.rawIR, .refinedIR, .llvmIR]
    }

    /// The minimum stage of compilation to produce this artifact.
    var minimumStage: Manifest.Stage {
      switch self {
      case .rawIR: .lowering
      case .refinedIR: .lowering
      case .llvmIR: .llvm
      case .executable: .execution
      }
    }

    /// The textual description of `self`.
    var description: String { rawValue }

    /// The order of `self` among all artifact tags, which is used to sort them.
    var order: Int {
      switch self {
      case .rawIR: 0
      case .refinedIR: 1
      case .llvmIR: 2
      case .executable: 3
      }
    }

    /// Returns true iff `l` is ordered before `r`.
    static func < (l: CompilerTests.ArtifactTag, r: CompilerTests.ArtifactTag) -> Bool {
      l.order < r.order
    }

  }

  /// The intermediate artifacts of a module's compilation and testing.
  ///
  /// Members shall be set after the corresponding stage is completed.
  private struct Artifacts {

    /// The textual artifacts of the compilation and testing pipeline, keyed by their tag.
    private(set) var textual = SortedDictionary<ArtifactTag, String>()

    /// The URL of the generated executable residing in a temporary directory, if any.
    ///
    /// The executable is copied to the test case destination if the compiler could produce one but
    /// the test failed.
    var executable: URL?

    /// Saves the artifacts into test-case-level observation files of `test`.
    func save(into test: TestDescription) throws {
      for (tag, artifact) in textual {
        try test.saveTestCaseLevelObservation(artifact, tag: tag.rawValue)
      }

      if let a: URL = executable {
        try? FileManager.default.removeItem(at: test.executableDestination())
        try FileManager.default.copyItem(at: a, to: test.executableDestination())
      }
    }

    /// Records the textual `artifact` as the artifact tagged `tag`.
    mutating func record(_ artifact: String, for tag: ArtifactTag) {
      textual[tag] = artifact
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

  /// Compiles and runs `input` expecting no compilation error.
  func positive(_ input: TestDescription) async throws {
    await loggingSourceOnFailure(root: input.root) {
      // Compile the input up until the specified stage.
      let o = input.manifest.optimizations != .none
      let r = try await compile(input, withOptimizations: o)
      try assertSansError(r.driver.program)

      // Should an executable be tested?
      if input.manifest.stage == .execution {
        let e = try XCTUnwrap(r.artifacts.executable)
        let x = try Process.execute(e)
        if input.manifest.shouldTrap {
          XCTAssert(x.terminationReason == .uncaughtSignal, "program did not trap")
        } else {
          assertExitStatus(x, describedBy: input)
        }
      }

      if testFailed || alwaysSaveArtifacts { try r.artifacts.save(into: input) }
    }
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: TestDescription) async throws {
    await loggingSourceOnFailure(root: input.root) {
      let r = try await compile(input, withOptimizations: false)
      let m = "program compiled but an error was expected.\nSource: \(input.root.path)\n"
      XCTAssert(r.driver.program.containsError, m)
      assertExpectations(r.expectedDiagnostics, r.driver.program.diagnostics)

      if testFailed || alwaysSaveArtifacts { try r.artifacts.save(into: input) }
    }
  }

  /// Executes `action`, and logs the test case's `root` on test failure for easier diagnostics.
  ///
  /// Also logs and catches any error thrown by `action`, failing the test case.
  private func loggingSourceOnFailure<T>(root: URL, _ action: () async throws -> T) async {
    do {
      _ = try await action()
      if testFailed {
        XCTFail("\nSource: \(root.path)\n")
      }
    } catch let e {
      XCTFail("\(e)\nSource: \(root.path)\n")
    }
  }

  /// Compiles `input` and returns the resulting artifacts.
  private func compile(
    _ input: TestDescription, withOptimizations optimized: Bool
  ) async throws -> CompilationResult {
    var driver = try Driver(
      moduleCachePath: CompilerTests.moduleCachePath.url, targetSpecification: .native())

    if input.manifest.requiresStandardLibrary {
      try await driver.loadStandardLibrary()
    }

    let m = driver.program.demandModule(.init("Test"))
    if input.manifest.requiresStandardLibrary {
      driver.program[m].addDependency(Module.standardLibraryName)
    }

    let (cSources, expectedDiagnostics) = try collectSources(input: input, m: &driver.program[m])

    var artifacts = Artifacts()
    do {
      try await compile(
        m, until: input.manifest.stage, using: &driver, withCSources: cSources,
        accumulatingArtifactsInto: &artifacts,
        expectedArtifacts: input.manifest.artifactExpectations)
    } catch let e {
      try artifacts.save(into: input)
      throw e
    }

    return .init(
      testCase: input,
      driver: driver,
      module: m,
      expectedDiagnostics: expectedDiagnostics,
      artifacts: artifacts)
  }

  /// Collects the Hylo sources into `m`, and returns the C sources and expected diagnostics per
  /// Hylo source file.
  func collectSources(
    input: TestDescription, m: inout Module
  ) throws -> (cSources: [URL], expectedDiagnostics: [FileName: String]) {
    var expectedDiagnostics: [FileName: String] = [:]
    var cSources: [URL] = []

    func addHyloSourceFile(at u: URL) throws {
      let source = try SourceFile(contentsOf: u)
      m.addSource(source)

      let v = u.deletingPathExtension().appendingPathExtension("diagnostics.expected")
      let expected = try? String(contentsOf: v, encoding: .utf8)
      expectedDiagnostics[source.name] = expected
    }

    if input.isPackage {
      let items = FileManager.default.enumerator(
        at: input.root,
        includingPropertiesForKeys: [.isRegularFileKey],
        options: [.skipsHiddenFiles, .skipsPackageDescendants])!

      for case let u as URL in items {
        if u.pathExtension == "hylo" {
          try addHyloSourceFile(at: u)
        } else if u.pathExtension == "c" {
          cSources.append(u)
        }
      }
    } else {
      try addHyloSourceFile(at: input.root)
    }

    return (cSources, expectedDiagnostics)
  }

  /// Compiles `m`, which is a module whose source have been parsed with `driver`, until `stage`,
  /// adding compilation artifacts to `artifacts`.
  private func compile(
    _ m: Module.ID, until stage: Manifest.Stage, using driver: inout Driver,
    withCSources cSources: [URL], accumulatingArtifactsInto artifacts: inout Artifacts,
    expectedArtifacts: SortedDictionary<ArtifactTag, String>
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
    let rawIR = driver.program.show(driver.program[m].ir)
    artifacts.record(rawIR, for: .rawIR)
    assertArtifact(.rawIR, expected: expectedArtifacts[.rawIR], observed: rawIR)

    // IR Transformation passes.
    let t = await driver.applyTransformationPasses(m)
    if t.containsError { return }
    let refinedIR = driver.program.show(driver.program[m].ir)
    artifacts.record(refinedIR, for: .refinedIR)
    assertArtifact(.refinedIR, expected: expectedArtifacts[.refinedIR],
      observed: refinedIR)
    if stage == .lowering { return }

    // LLVM Lowering.
    if (try driver.compileToLLVM(m)).containsError { return }
    let llvmIR = driver.llvmIR(of: m)!
    artifacts.record(llvmIR, for: .llvmIR)
    assertArtifact(.llvmIR, expected: expectedArtifacts[.llvmIR], observed: llvmIR)
    if stage == .llvm { return }

    // When the stdlib can be compiled, lower it to LLVM so generateExecutable can link it.
    // let stdlibID = driver.program.demandModule(Module.standardLibraryName)
    // if await driver.lower(stdlibID).containsError { return done() }
    // if await driver.applyTransformationPasses(stdlibID).containsError { return done() }
    // if (try driver.lowerToLLVM(stdlibID)).containsError { return done() }

    if stage == .execution {
      let outputDirectory = try FileManager.default.createUniqueTemporaryDirectory()
      let executable = outputDirectory.appendingPathComponent(driver.program[m].name)
      _ = try driver.generateExecutable(from: m, withCSources: cSources, writingTo: executable)
      artifacts.executable = executable
    }
  }

  /// Asserts that the `observed` artifact tagged `tag` matches `expected`, if present.
  private func assertArtifact(_ tag: ArtifactTag, expected: String?, observed: String) {
    guard let e = expected else { return }

    for c in IRMatching.comparisons(expected: e, observed: observed) {
      guard let o = c.observed else {
        XCTFail("No section in observed \(tag) matches:\n```\(c.expected)```\n")
        continue
      }

      XCTAssertEqual(o, c.expected, "\(tag) did not meet expectations.")
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

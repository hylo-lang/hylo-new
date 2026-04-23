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

  /// Iff true, intermediate compilation artifacts are saved even if test cases pass.
  let alwaysSaveArtifacts = false

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
    }

  }

  /// The test case currently being run.
  private var testCase: TestDescription? = nil

  /// The intermediate compilation artifacts.
  private var artifacts: Artifacts = .init()

  /// Saves any available compilation artifacts on test failure
  /// or if `alwaysSaveArtifacts` is true to facilitate diagnosis.
  ///
  /// Run by XCTest after each test case.
  override func tearDownWithError() throws {
    if let testRun, testRun.failureCount > 0 || alwaysSaveArtifacts, let testCase {
      try artifacts.save(into: testCase)
    }
  }

  /// Compiles `input` expecting no compilation error.
  func positive(_ input: TestDescription) async throws {
    let (program, _) = try await compile(input)
    assertSansError(program)
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: TestDescription) async throws {
    let (program, expectations) = try await compile(input)
    XCTAssert(program.containsError, "program compiled but an error was expected")
    assertExpectations(expectations, program.diagnostics)
  }

  /// Compiles `input` into `p` and returns expected diagnostics for each compiled source file.
  ///
  /// Sets up the `testCase` context and populates `artifacts` as soon as compilation stages succeed.
  private func compile(_ input: TestDescription) async throws -> (Program, [FileName: String]) {
    self.testCase = input

    var driver = Driver(moduleCachePath: CompilerTests.moduleCachePath.url)

    if input.manifest.requiresStandardLibrary {
      try await driver.load(Module.standardLibraryName, withSourcesAt: localStandardLibrarySources)
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

    func done() -> (Program, [FileName: String]) {
      (driver.program, expectedDiagnostics)
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

    // Code generation.
    assert(input.manifest.stage == .codegen)
    return done()
  }

  private func compile(_ m: Module.ID, driver: inout Driver) {

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
  private func assertSansError(_ program: Program) {
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
    XCTFail(report)
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

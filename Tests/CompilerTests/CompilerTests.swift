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

  /// The input of a compiler test.
  struct TestDescription {

    /// A test manifest.
    struct Manifest: Decodable {

      /// The options with which the input should be compiled.
      let options: [String]?

    }

    /// The root path of the program's sources.
    let root: URL

    /// The manifest of the test.
    let manifest: Manifest

    /// Creates an instance with the given properties.
    init(_ path: String) {
      self.root = URL(filePath: path)

      if root.pathExtension == "package" {
        self.manifest = (try? Self.manifest(root)) ?? .init(options: [])
      } else if let s = Self.firstLine(of: root), s.starts(with: "//!") {
        self.manifest = .init(options: s.split(separator: " ").dropFirst().map(String.init(_:)))
      } else {
        self.manifest = .init(options: [])
      }
    }

    /// `true` iff `self` describes a package.
    var isPackage: Bool {
      root.pathExtension == "package"
    }

    /// `true` iff `self` requires a standard library.
    var requiresStandardLibrary: Bool {
      if let options = manifest.options {
        return !options.contains("no-std")
      } else {
        return true
      }
    }

    /// Calls `action` on each Hylo source URL in the program described by `self`.
    func forEachSourceURL(_ action: (URL) throws -> Void) throws {
      if isPackage {
        try SourceFile.forEachURL(in: root, action)
      } else {
        try action(root)
      }
    }

    /// Returns the manifest of the test case at `root`.
    private static func manifest(_ root: URL) throws -> Manifest {
      // Try to read the actual manifest.
      if root.pathExtension == "package" {
        let json = try Data(contentsOf: root.appendingPathComponent("package.json"))
        return try JSONDecoder().decode(Manifest.self, from: json)
      }

      // Try to read the manifest's properties from the first line.
      else if let s = firstLine(of: root), s.starts(with: "//!") {
        return .init(options: s.split(separator: " ").dropFirst().map(String.init(_:)))
      }

      // Return a default manifest.
      else {
        return .init(options: [])
      }
    }

    /// Returns the first line of the file at `url`, which is encoded in UTF-8, or `nil`if that
    /// this file could not be read.
    private static func firstLine(of url: URL) -> Substring? {
      (try? String(contentsOf: url, encoding: .utf8))?.firstLine
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
  private func compile(_ input: TestDescription) async throws -> (Program, [FileName: String]) {
    var driver = Driver(moduleCachePath: CompilerTests.moduleCachePath.url)

    let requiresStandardLibrary = input.requiresStandardLibrary
    if requiresStandardLibrary {
      try await driver.load(.standardLibrary, withSourcesAt: standardLibrarySources)
    }

    let m = driver.program.demandModule(.init("Test"))
    if requiresStandardLibrary {
      driver.program[m].addDependency(.standardLibrary)
    }

    var expectations: [FileName: String] = [:]
    try input.forEachSourceURL { (u) in
      let source = try SourceFile(contentsOf: u)
      driver.program[m].addSource(source)

      let v = u.deletingPathExtension().appendingPathExtension("expected")
      let expected = try? String(contentsOf: v, encoding: .utf8)
      expectations[source.name] = expected
    }

    // Exit if there are parsing errors.
    if driver.program[m].containsError { return (driver.program, expectations) }

    // Semantic analysis.
    await driver.assignScopes(of: m)
    await driver.assignTypes(of: m)

    return (driver.program, expectations)
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
          let v = u.deletingPathExtension().appendingPathExtension("observed")
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

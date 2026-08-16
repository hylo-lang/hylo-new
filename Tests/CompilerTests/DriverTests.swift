@testable import Driver
import SwiftyLLVM
import XCTest
import FrontEnd

final class DriverTests: XCTestCase {

  func testHostDriverCreation() throws {
    let driver = try Driver(targetSpecification: .host())

    // Should be generic
    XCTAssertEqual("", driver.target.cpu)
    XCTAssertEqual("", driver.target.features)
  }

  func testNativeDriverCreation() throws {
    let driver = try Driver(targetSpecification: .native())
    XCTAssertFalse(driver.target.cpu.isEmpty)
  }

  func testCreateDriverWithOptions() throws {
    let driver = try Driver(
      targetSpecification: .host(),
      optimization: .aggressive,
      relocation: .pic,
      codeModel: .small)
    XCTAssertEqual(driver.optimization, .aggressive)
    XCTAssertEqual(driver.relocation, .pic)
    XCTAssertEqual(driver.codeModel, .small)
  }

  func testModuleCacheDisabled() throws {
    let d = try Driver(moduleCachePath: nil, targetSpecification: .native())
    XCTAssertNil(d.cachedArchive(of: "test"))
  }

  func testModuleCacheNotFound() throws {
    let d = try Driver(
      moduleCachePath: FileManager.default.temporaryDirectory,
      targetSpecification: .native())
    XCTAssertNil(d.cachedArchive(of: "test"))
  }

  func testCircularDependencyGraph() throws {
    // Tests that a dependency graph with a cycle is detected and reported as an error.
    try FileManager.default.withUniqueTemporaryDirectory { (root) in
      try writeArchives(withDependencies: [("A", ["B"]), ("B", ["A"])], into: root)

      var d = try Driver(targetSpecification: .host(), moduleSearchPaths: [root])
      XCTAssertThrowsError(try d.loadArchivedModule("A")) { (e) in
        XCTAssertEqual(
          (e as? Driver.Error)?.message,
          "circular dependency detected while loading module 'A'")
      }
    }
  }

  func testDiamondDependencyGraph() throws {
    // Tests that a diamond dependency graph is serialized and loaded correctly.
    try FileManager.default.withUniqueTemporaryDirectory { (root) in
      try writeArchives(
        withDependencies: [("A", ["B", "C"]), ("B", ["D"]), ("C", ["D"]), ("D", [])], into: root)

      var driver = try Driver(targetSpecification: .host(), moduleSearchPaths: [root])
      let a = try driver.loadArchivedModule("A")

      XCTAssertEqual(driver.program.identity(module: "A"), a)
      XCTAssertEqual(driver.program.modules.count, 4)
      XCTAssertEqual(driver.program[a].dependencies, ["B", "C"])

      let b = try XCTUnwrap(driver.program.identity(module: "B"))
      XCTAssertEqual(driver.program[b].dependencies, ["D"])
      let c = try XCTUnwrap(driver.program.identity(module: "C"))
      XCTAssertEqual(driver.program[c].dependencies, ["D"])
      let d = try XCTUnwrap(driver.program.identity(module: "D"))
      XCTAssertEqual(driver.program[d].dependencies, [])

      // Loading a module that is already in the program has no effect.
      XCTAssertEqual(try driver.loadArchivedModule("A"), a)
    }
  }

  // A program's dependency graph.
  typealias DependencyGraph = [(module: FrontEnd.Module.Name, dependencies: [FrontEnd.Module.Name])]

  /// Writes the archives of empty modules having the dependencies described by `graph` into
  /// `directory`, using a scratch driver.
  private func writeArchives(withDependencies graph: DependencyGraph, into directory: URL) throws {
    var driver = try Driver(targetSpecification: .host())

    // Create the modules of `graph`.
    for (m, _) in graph { _ = driver.program.demandModule(m) }

    // Set up the dependencies between modules according to `graph`.
    for (m, dependencies) in graph {
      let i = driver.program.identity(module: m)!
      for d in dependencies { driver.program[i].addDependency(d) }
    }

    // Write the archives to disk.
    for (m, _) in graph {
      let i = driver.program.identity(module: m)!
      try driver.writeArchive(of: i, to: directory.appending(path: m + ".hylomodule"))
    }
  }

  func testInvalidCachedArchive() async throws {
    // An invalid cached archive is recompiled from sources and overwritten.
    try await FileManager.default.withUniqueTemporaryDirectory { (cacheRoot) in
      try await FileManager.default.withUniqueTemporaryDirectory { (sourceRoot) in
        var d = try Driver(
          moduleCachePath: cacheRoot,
          targetSpecification: .native())

        let cachePath = cacheRoot.appendingPathComponent("Main.hylomodule")
        // Write an invalid archive
        try "invalid".write(to: cachePath, atomically: true, encoding: .utf8)

        XCTAssertNotNil(d.cachedArchive(of: "Main"))

        // The corrupt entry is treated as a miss: the module is compiled from sources and its
        // archive is rewritten.
        try await d.load("Main", withSourcesAt: sourceRoot)
        XCTAssertNotNil(d.program.identity(module: "Main"))

        let healed = try XCTUnwrap(d.cachedArchive(of: "Main"))
        XCTAssertNotEqual(healed, Data("invalid".utf8))

        // The rewritten archive is loadable by a fresh driver.
        var e = try Driver(moduleCachePath: cacheRoot, targetSpecification: .native())
        try await e.load("Main", withSourcesAt: sourceRoot)
        XCTAssertNotNil(e.program.identity(module: "Main"))
      }
    }
  }

  func testNoImportsFromCache() throws {
    // Tests that imports are not resolved from the module cache.
    try FileManager.default.withUniqueTemporaryDirectory { (cacheRoot) in
      try writeArchives(withDependencies: [("A", [])], into: cacheRoot)

      // The archive is in the cache but in no module search path.
      var d = try Driver(moduleCachePath: cacheRoot, targetSpecification: .host())
      XCTAssertNotNil(d.cachedArchive(of: "A"))
      XCTAssertThrowsError(try d.loadArchivedModule("A")) { (e) in
        XCTAssertEqual(
          (e as? Driver.Error)?.message,
          "no archive found for module 'A' in module search paths []")
      }
    }
  }

  func testUnreadableArchive() throws {
    try FileManager.default.withUniqueTemporaryDirectory { (root) in
      // A directory named like an archive exists but cannot be read as a file.
      try FileManager.default.createDirectory(
        at: root.appending(path: "A.hylomodule"), withIntermediateDirectories: true)

      var d = try Driver(targetSpecification: .host(), moduleSearchPaths: [root])
      XCTAssertThrowsError(try d.loadArchivedModule("A")) { (e) in
        let m = (e as? Driver.Error)?.message ?? ""
        XCTAssert(m.contains("cannot read module archive at"), "unexpected message: \(m)")
      }
    }
  }

  func testInvalidArchiveContents() throws {
    try FileManager.default.withUniqueTemporaryDirectory { (root) in
      let f = root.appending(path: "A.hylomodule")
      try "invalid".write(to: f, atomically: true, encoding: .utf8)

      var d = try Driver(targetSpecification: .host(), moduleSearchPaths: [root])
      XCTAssertThrowsError(try d.loadArchivedModule("A")) { (e) in
        let m = (e as? Driver.Error)?.message ?? ""
        XCTAssert(
          m.contains("Failed to parse the module archive of 'A' at '\(f.path)'"),
          "unexpected message: \(m)")
      }
    }
  }

}

final class CompilationErrorTests: XCTestCase {

  func testStringRepresentation() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(.error, "bang", at: s)
    let c = CompilationError(diagnostics: DiagnosticSet(CollectionOfOne(e)))

    XCTAssertEqual(
      "\(c)",
      """

      virtual:///1ssiyy33rbj6z:1.1-3: error: bang
      Hello.
      ~~

      """)

  }

}

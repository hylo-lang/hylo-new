@testable import Driver
import Foundation
import SwiftyLLVM
import Testing
import FrontEnd

struct DriverTests {

  @Test func hostDriverCreation() throws {
    let driver = try Driver(targetSpecification: .host())

    // Should be generic
    #expect(driver.target.cpu == "")
    #expect(driver.target.features == "")
  }

  @Test func nativeDriverCreation() throws {
    let driver = try Driver(targetSpecification: .native())
    #expect(driver.target.cpu != "")
  }

  @Test func createDriverWithOptions() throws {
    let driver = try Driver(
      targetSpecification: .host(),
      optimization: .aggressive,
      relocation: .pic,
      codeModel: .small)
    #expect(driver.optimization == .aggressive)
    #expect(driver.relocation == .pic)
    #expect(driver.codeModel == .small)
  }

  @Test func moduleCacheDisabled() throws {
    let d = try Driver(moduleCachePath: nil, targetSpecification: .native())
    #expect(d.archive(of: "test") == nil)
  }

  @Test func moduleCacheNotFound() throws {
    let d = try Driver(
      moduleCachePath: FileManager.default.temporaryDirectory,
      targetSpecification: .native())
    #expect(d.archive(of: "test") == nil)
  }

  @Test func invalidArchive() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (cacheRoot) in
      try await FileManager.default.withUniqueTemporaryDirectory { (sourceRoot) in
        var d = try Driver(
          moduleCachePath: cacheRoot,
          targetSpecification: .native())

        let cachePath = cacheRoot.appendingPathComponent("Main.hylomodule")
        // Write an invalid archive
        try "invalid".write(to: cachePath, atomically: true, encoding: .utf8)

        #expect(d.archive(of: "Main") != nil)

        // Now try to load it - this should fail
        do {
          try await d.load("Main", withSourcesAt: sourceRoot)
          Issue.record("Expected load to fail")
        } catch let error as Driver.Error {
          guard case .invalidModuleArchive(let module, let location) = error else {
            throw error
          }
          #expect(module == "Main")
          #expect(location == cacheRoot)

          #expect("\(error)" == """
            Failed to parse module archive of 'Main' at '\(cacheRoot)'.

            Maybe the archive was compiled with a different version of the compiler. \
            Try erasing the module cache.
            """)
        }
      }
    }
  }

}

struct CompilationErrorTests {

  @Test func stringRepresentation() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(.error, "bang", at: s)
    let c = CompilationError(diagnostics: DiagnosticSet(CollectionOfOne(e)))

    #expect(
      "\(c)" == """

      virtual:///1ssiyy33rbj6z:1.1-3: error: bang
      Hello.
      ~~

      """)

  }

}

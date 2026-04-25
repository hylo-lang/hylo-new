import Driver
import SwiftyLLVM
import XCTest

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
    XCTAssertNil(d.archive(of: "test"))
  }

  func testModuleCacheNotFound() throws {
    let d = try Driver(
      moduleCachePath: FileManager.default.temporaryDirectory, 
      targetSpecification: .native())
    XCTAssertNil(d.archive(of: "test"))
  }

  func testInvalidArchive() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (cacheRoot) in 
      try await FileManager.default.withUniqueTemporaryDirectory { (sourceRoot) in
        var d = try Driver(
          moduleCachePath: cacheRoot, 
          targetSpecification: .native())
        
        let cachePath = cacheRoot.appendingPathComponent("Main.hylomodule")
        // Write an invalid archive
        try "invalid".write(to: cachePath, atomically: true, encoding: .utf8)

        XCTAssertNotNil(d.archive(of: "Main"))


        // Now try to load it - this should fail
        do {
          try await d.load("Main", withSourcesAt: sourceRoot)
          XCTFail("Expected load to fail")
        } catch let error as Driver.Error {
          XCTAssertEqual(error.message, """
            Failed to parse module archive of 'Main' at '\(cacheRoot)'.

            Maybe the archive is compiled using a different version of the compiler. Try erasing the module cache.
            """)

          XCTAssertEqual("\(error)", error.message)
        }
      }
    }
  }

}

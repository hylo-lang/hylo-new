import FrontEnd
import XCTest
import Driver
import StandardLibrary

final class StandardLibraryLoadingTests: XCTestCase {

  func testStandardLibraryLoading() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.loadStandardLibrary()
  }

  func testStandardLibraryLoadingBundled() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.load(
      Module.standardLibraryName, withSourcesAt: bundledStandardLibrarySources)
  }

  func testStandardLibraryLoadingLocal() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.load(
      Module.standardLibraryName, withSourcesAt: localStandardLibrarySources,
      additionalSources: [SourceFile(contentsOf: generatedStandardLibrarySource)])
  }

  func testStandardLibraryCompilesToLLVM() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.loadStandardLibrary()
    let m = try XCTUnwrap(driver.program.identity(module: Module.standardLibraryName))
    let r = try driver.compileToLLVM(m)
    XCTAssertFalse(r.containsError)
  }

}

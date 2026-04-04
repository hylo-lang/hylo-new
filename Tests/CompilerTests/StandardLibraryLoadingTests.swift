import FrontEnd
import XCTest
import Driver
import StandardLibrary

final class StandardLibraryLoadingTests: XCTestCase {
  func testStandardLibraryLoading() async throws {
    var driver = Driver()
    try await driver.loadStandardLibrary()
  }

  func testStandardLibraryLoadingBundled() async throws {
    var driver = Driver()
    try await driver.load(Module.standardLibraryName, withSourcesAt: bundledStandardLibrarySources)
  }

  func testStandardLibraryLoadingLocal() async throws {
    var driver = Driver()
    try await driver.load(Module.standardLibraryName, withSourcesAt: standardLibrarySources)
  }
}

import Driver
import XCTest

@testable import FrontEnd

/// A collection of tests that checks mangling/demangling for the standard library.
final class StandardLibraryManglingTests: XCTestCase {

  /// Checks that we can mangle and demangle without errors
  /// all the declarations in the standard library.
  func testStandardLibraryMangling() async throws {
    var driver = Driver(moduleCachePath: Self.moduleCachePath.url)
    try await driver.loadStandardLibrary()

    let m = driver.program.modules[.standardLibrary]!
    for s in m.syntax {
      if driver.program.isDeclaration(s) {
        let d = DeclarationIdentity(uncheckedFrom: s)
        let mangled = driver.program.mangled(d)
        let demangled = DemangledSymbol(mangled).description
        XCTAssertFalse(
          demangled.contains("?"),
          "demangling of \(mangled) contains errors: \(demangled)"
        )
      }
    }
  }

  /// A temporary folder for caching compilation artifacts during testing.
  ///
  /// An new directory is generated every time this property is initialized and removed once all
  /// tests have run.
  private static let moduleCachePath = Driver.temporaryModuleCachePath()

  /// Deletes cached compilation artifacts.
  override class func tearDown() {
    moduleCachePath.delete()
  }
}

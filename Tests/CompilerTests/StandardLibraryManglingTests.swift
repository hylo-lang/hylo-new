import Driver
import Testing

@testable import FrontEnd

/// A collection of tests that checks mangling/demangling for the standard library.
struct StandardLibraryManglingTests {

  /// Tests the mangling and demangling of all the declarations in the standard library.
  @Test func standardLibraryMangling() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.installCachedStandardLibrary()

    let m = driver.program.modules[Module.standardLibraryName]!
    for s in m.syntax {
      if driver.program.isDeclaration(s) {
        let d = DeclarationIdentity(uncheckedFrom: s)
        let mangled = driver.program.mangled(d)
        let demangled = DemangledSymbol(mangled).description
        #expect(
          !demangled.contains("#!"),
          "demangling of \(mangled) contains errors: \(demangled)"
        )
      }
    }
  }

}

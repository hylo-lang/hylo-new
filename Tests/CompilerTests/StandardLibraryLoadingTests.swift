import FrontEnd
import Testing
import Driver
import StandardLibrary

struct StandardLibraryLoadingTests {

  @Test func standardLibraryLoading() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.loadStandardLibrary()
  }

  @Test func standardLibraryLoadingBundled() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.load(
      Module.standardLibraryName, withSourcesAt: bundledStandardLibrarySources,
      additionalSources: [SourceFile(contentsOf: generatedStandardLibrarySource)])
  }

  @Test func standardLibraryLoadingLocal() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.load(
      Module.standardLibraryName, withSourcesAt: localStandardLibrarySources,
      additionalSources: [SourceFile(contentsOf: generatedStandardLibrarySource)])
  }

}

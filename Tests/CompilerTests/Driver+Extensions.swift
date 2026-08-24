import Driver
import Foundation
import FrontEnd
import Testing
import Utilities

/// The program containing the standard library, initialized exactly once per process.
///
/// The standard library is loaded from the archive cache if an up-to-date archive exists and
/// compiled from its sources otherwise.
private let sharedStandardLibrary = Task { () throws -> Program in
  return try await standardLibraryProgram()
}

extension Driver {

  /// Replaces the `program` of `self` with the process-wide cache of the standard library.
  mutating func installCachedStandardLibrary() async throws {
    installStandardLibrary(from: try await sharedStandardLibrary.value)
  }

}

/// A suite trait that initializes the process-wide standard library cache before any test in the
/// suite starts, so that the setup time is excluded from individual test timings.
struct StandardLibraryWarmup: SuiteTrait, TestScoping {

  /// Initializes the shared standard library caches, then executes the test suite.
  func provideScope(
    for test: Test, testCase: Test.Case?, performing testSuite: @Sendable () async throws -> Void
  ) async throws {
    _ = try await sharedStandardLibrary.value
    try await testSuite()
  }

}

extension Testing.Trait where Self == StandardLibraryWarmup {

  /// A trait that initializes the standard library cache before any test in the suite starts.
  static var standardLibraryWarmup: Self { Self() }

}

/// Returns a program containing the standard library, loaded from the archive cache or compiled
/// from its sources.
private func standardLibraryProgram() async throws -> Program {
  var d = try Driver(moduleCachePath: try sharedModuleCachePath(), targetSpecification: .native())
  try await d.loadStandardLibrary()
  return d.program
}

/// Returns a stable folder for caching compilation artifacts, persistent across test runs
/// with the same compiler.
private func sharedModuleCachePath() throws -> URL {
  let root = URL(filePath: #filePath)
    .deletingLastPathComponent()
    .deletingLastPathComponent()
    .deletingLastPathComponent()  
    .appending(components: ".build", "hylo-test-module-cache")
  let key = try compilerFingerprint()
  let path = root.appending(component: key)

  let m = FileManager.default
  try m.createDirectory(at: path, withIntermediateDirectories: true)

  // Remove caches left over by other compiler builds.
  if let entries = try? m.contentsOfDirectory(at: root, includingPropertiesForKeys: nil) {
    for e in entries where e.lastPathComponent != key {
      try? m.removeItem(at: e)
    }
  }

  return path
}

/// Returns a fingerprint of the compiler under test, derived from the `hc` executable built
/// alongside the test bundle.
///
/// The fingerprint captures the executable's path, last modification time, and file size. Unlike
/// the test binary—which all test targets link into—`hc` is relinked only when the compiler's
/// code changes, so the fingerprint is stable across edits to test code.
private func compilerFingerprint() throws -> String {
  let binary = try compilerBinary()
  let a = try FileManager.default.attributesOfItem(atPath: binary.path)
  guard let d = a[.modificationDate] as? Date, let s = a[.size] as? NSNumber else {
    throw TestEnvironmentError("no modification date or size for '\(binary.path)'")
  }

  var h = FNV1.native()
  h.combine(binary.path)
  h.combine(d.timeIntervalSince1970.bitPattern)
  h.combine(s.uint64Value)
  return String(UInt(bitPattern: h.state), radix: 16)
}

/// Returns the path of the `hc` executable in the build folder containing the test bundle.
private func compilerBinary() throws -> URL {
  // On Linux the test binary sits directly in the build folder; on macOS it is nested inside an
  // .xctest bundle, hence the upward search.
  var d = currentBinary().deletingLastPathComponent()
  for _ in 0 ..< 4 {
    let c = d.appending(component: "hc")
    if FileManager.default.isExecutableFile(atPath: c.path) { return c }
    d = d.deletingLastPathComponent()
  }
  throw TestEnvironmentError(
    "no 'hc' executable found next to '\(currentBinary().path)'; run the tests with 'swift test'")
}

/// Returns the path to the binary in which this code is running.
private func currentBinary() -> URL {
  Bundle(for: BundleToken.self).executableURL ??
    URL(fileURLWithPath: Swift.CommandLine.arguments[0])
}

/// A token used to locate the bundle containing the test.
private final class BundleToken {}

/// An error indicating that the environment running the tests is not set up as expected.
private struct TestEnvironmentError: Error, CustomStringConvertible {

  /// A description of the defect.
  let description: String

  /// Creates an instance with the given description.
  init(_ description: String) {
    self.description = description
  }

}

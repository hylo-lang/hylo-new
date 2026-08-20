import ArgumentParser
import Foundation
import FrontEnd
import Subprocess
import Utilities
import XCTest

/// End-to-end tests running `hc` as a subprocess.
final class CommandLineEndToEndTests: XCTestCase {

  func testSuccessfulCompilation() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let main = try write("public fun main() {}", to: root.appending(path: "main.hylo"))
      let r = try await hc(["--emit", "object", "-o", "out.o", main.path], in: root)

      XCTAssertEqual(r.exitCode, 0, r.standardError)
      XCTAssert(FileManager.default.fileExists(atPath: root.appending(path: "out.o").path))

      // The product's archive is not written to the module cache.
      let cached = try Self.cachedArchives()
      XCTAssert(cached.allSatisfy({ (m) in m == Module.standardLibraryName }), "\(cached)")
    }
  }

  func testValidationFailureCode() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let main = try write("public fun main() {}", to: root.appending(path: "main.hylo"))
      let r = try await hc(
        ["--emit", "ast", "--emit-module-to", "M.hylomodule", main.path],
        in: root, cache: .disabled)

      XCTAssertEqual(r.exitCode, ExitCode.validationFailure.rawValue)
      XCTAssert(
        r.standardError.contains("'--emit-module-to' cannot be used with '--emit ast'"),
        r.standardError)
      XCTAssert(r.standardError.contains("Usage:"), r.standardError)
    }
  }

  func testCompilationFailure() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let main = try write(
        "public fun main() { undefinedFunction() }", to: root.appending(path: "main.hylo"))
      let r = try await hc(["--emit", "object", "-o", "out.o", main.path], in: root)

      XCTAssertEqual(r.exitCode, ExitCode.failure.rawValue)
      XCTAssert(r.standardError.contains("undefined symbol 'undefinedFunction'"), r.standardError)
      XCTAssert(!FileManager.default.fileExists(atPath: root.appending(path: "out.o").path))
    }
  }

  func testEffectiveModuleName() async throws {
    // A single source file: the module is named after the file.
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let main = try write("public fun main() {}", to: root.appending(path: "a.hylo"))
      let r = try await hc(["--emit", "object", main.path], in: root)

      XCTAssertEqual(r.exitCode, 0, r.standardError)
      XCTAssert(FileManager.default.fileExists(atPath: root.appending(path: "a.o").path))
    }

    // A directory: the module is named 'Main'.
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      try write("public fun main() {}", to: root.appending(path: "src/a.hylo"))
      let r = try await hc(["--emit", "object", "src/"], in: root)

      XCTAssertEqual(r.exitCode, 0, r.standardError)
      XCTAssert(FileManager.default.fileExists(atPath: root.appending(path: "Main.o").path))
    }

    // Multiple source files: the module is named 'Main'.
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let a = try write("public fun main() {}", to: root.appending(path: "a.hylo"))
      let b = try write("public fun f() {}", to: root.appending(path: "b.hylo"))
      let r = try await hc(["--emit", "object", a.path, b.path], in: root)

      XCTAssertEqual(r.exitCode, 0, r.standardError)
      XCTAssert(FileManager.default.fileExists(atPath: root.appending(path: "Main.o").path))
    }
  }

  func testModuleArchiveRoundTrip() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      try write(
        "public fun double(_ x: Int) -> Int { x + x }",
        to: root.appending(path: "util/util.hylo"))
      try write(
        """
        import Util

        public fun main() {
          let _ = double(x: 21)
        }
        """,
        to: root.appending(path: "app/main.hylo"))

      let u = try await hc(
        [
          "--module-name", "Util", "--emit-module-to", "Util.hylomodule",
          "--emit", "object", "-o", "Util.o", "util/",
        ],
        in: root)
      XCTAssertEqual(u.exitCode, 0, u.standardError)
      XCTAssert(fileExists(atPath: root.appending(path: "Util.hylomodule").path))

      let a = try await hc(
        [
          "--import", "Util", "--module-search-path", ".", "--emit",
          "object", "-o", "App.o", "app/"
        ], in: root)
      XCTAssertEqual(a.exitCode, 0, a.standardError)
      XCTAssert(fileExists(atPath: root.appending(path: "App.o").path))
    }
  }

  func testImportWithoutSearchPath() async throws {
    // Import without a search path should fail.
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let main = try write("public fun main() {}", to: root.appending(path: "main.hylo"))
      let r =
        try await hc(["--import", "Util", "--emit", "object", "-o", "out.o", main.path], in: root)

      XCTAssertNotEqual(r.exitCode, 0)
      XCTAssert(
        r.standardError.contains("no archive found for module 'Util' in module search paths []"),
        r.standardError)
    }
  }

  func testCorruptImportedArchive() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let archive = root.appending(path: "A.hylomodule")
      try write("invalid", to: archive)
      let main = try write("public fun main() {}", to: root.appending(path: "main.hylo"))
      let r = try await hc(
        [
          "--import", "A", "--module-search-path", ".", "--emit", "object",
          "-o", "out.o", main.path
        ], in: root)

      XCTAssertNotEqual(r.exitCode, 0)
      XCTAssert(
        r.standardError.contains("Failed to parse the module archive of 'A' at '"),
        r.standardError)
    }
  }

  func testSelfHealingCache() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let cache = root.appending(path: "cache")
      try FileManager.default.createDirectory(at: cache, withIntermediateDirectories: true)
      let main = try write("public fun main() {}", to: root.appending(path: "main.hylo"))
      let entry = cache.appending(path: Module.standardLibraryName + ".hylomodule")

      // A cold run populates the cache with the standard library's archive.
      let cold =
        try await hc(["--emit", "ast", "-o", "out.ast", main.path], in: root, cache: .at(cache))
      XCTAssertEqual(cold.exitCode, 0, cold.standardError)
      XCTAssert(fileExists(atPath: entry.path))

      // A corrupted entry is recompiled and overwritten rather than reported as an error.
      try write("corrupt", to: entry)
      let healed =
        try await hc(["--emit", "ast", "-o", "out.ast", main.path], in: root, cache: .at(cache))
      XCTAssertEqual(healed.exitCode, 0, healed.standardError)
      let contents = try Data(contentsOf: entry)
      XCTAssertNotEqual(contents, Data("corrupt".utf8))
    }
  }

  func testDeterministicArtifacts() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let main = try write(
        """
        public fun double(_ x: Int) -> Int { x + x }

        public fun main() {
          let _ = double(x: 21)
        }
        """,
        to: root.appending(path: "main.hylo"))

      func emit(withSuffix suffix: String) async throws -> (archive: Data, hash: Data) {
        // We must compile without module caches, otherwise the compilation conditions may change
        // between the commands (compiling standard library from source vs deserializing).
        let r = try await hc(
          [
            "--emit", "object", "-o", "out\(suffix).o",
            "--emit-module-to", "M\(suffix).hylomodule",
            "--emit-module-interface-hash-to", "M\(suffix).hash",
            main.path,
          ],
          in: root, cache: .disabled)
        XCTAssertEqual(r.exitCode, 0, r.standardError)
        return (
          try Data(contentsOf: root.appending(path: "M\(suffix).hylomodule")),
          try Data(contentsOf: root.appending(path: "M\(suffix).hash")))
      }

      let first = try await emit(withSuffix: "1")
      let second = try await emit(withSuffix: "2")
      XCTAssertEqual(first.archive, second.archive)
      XCTAssertEqual(first.hash, second.hash)
    }
  }

  func testDefaultCacheRootFromEnvironment() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let cacheRoot = root.appending(path: "workspace-cache")
      let main = try write("public fun main() {}", to: root.appending(path: "main.hylo"))

      // Without '--module-cache', the cache is a 'hylo' directory created in the root denoted by
      // the environment.
      let r = try await hc(
        ["--emit", "ast", "-o", "out.ast", main.path], in: root, cache: .implicit,
        environment: .inherit.updating(["HYLO_DEFAULT_CACHE_ROOT": cacheRoot.path]))
      XCTAssertEqual(r.exitCode, 0, r.standardError)

      // The default cache root is populated with the standard library's archive.
      let archive = cacheRoot
        .appending(path: "hylo")
        .appending(path: Module.standardLibraryName + ".hylomodule")
      XCTAssert(fileExists(atPath: archive.path), "no cache entry at \(archive.path)")
    }
  }

  func testPrintStdlibRoot() async throws {
    try await FileManager.default.withUniqueTemporaryDirectory { (root) in
      let r = try await hc(["--print-stdlib-root"], in: root, cache: .disabled)

      XCTAssertEqual(r.exitCode, 0, r.standardError)
      let path = r.standardOutput.trimmingCharacters(in: .whitespacesAndNewlines)
      XCTAssert(directoryExists(atPath: path))
    }
  }

  // MARK: - Harness

  /// The module cache shared by the tests in this suite, so that the standard library is compiled
  /// at most once.
  private static let moduleCache: (url: URL, delete: @Sendable () -> Void) = {
    let m = FileManager.default
    let u = try! m.url(
      for: .itemReplacementDirectory, in: .userDomainMask,
      appropriateFor: m.temporaryDirectory, create: true)
    return (u, { try? FileManager.default.removeItem(at: u) })
  }()

  /// The location of the `hc` executable built alongside the test runner.
  private static let hcExecutable: URL = {
    #if os(macOS)
    let bundle = Bundle.allBundles.first(where: { (b) in b.bundlePath.hasSuffix(".xctest") })!
    return bundle.bundleURL.deletingLastPathComponent().appending(path: "hc")
    #else
    return Bundle.main.bundleURL.appending(path: "hc")
    #endif
  }()

  override class func tearDown() {
    moduleCache.delete()
    super.tearDown()
  }

  /// The way a test invocation of `hc` selects its module cache.
  private enum CacheOption {

    /// Pass `--module-cache <url>`.
    case at(URL)

    /// Pass `--no-caching`.
    case disabled

    /// Pass no cache-related option, letting `hc` choose its default cache.
    case implicit

    /// The command-line arguments corresponding to `self`.
    var arguments: [String] {
      switch self {
      case .at(let u): ["--module-cache", u.path]
      case .disabled: ["--no-caching"]
      case .implicit: []
      }
    }

  }

  /// Runs `hc` with `arguments` and `environment` in `workingDirectory` and returns its execution
  /// report.
  ///
  /// Unless `cache` is `.implicit`, the corresponding option is appended to `arguments` so that
  /// tests never touch the user's actual cache; it defaults to a cache shared by the whole suite.
  @discardableResult
  private func hc(
    _ arguments: [String], in workingDirectory: URL,
    cache: CacheOption = .at(CommandLineEndToEndTests.moduleCache.url),
    environment: Environment = .inherit
  ) async throws -> ExecutionReport {
    try await executeSubprocess(
      .path(Self.hcExecutable), arguments: arguments + cache.arguments,
      workingDirectory: workingDirectory, environment: environment)
  }

  /// Writes `contents` to `url`, creating intermediate directories, and returns `url`.
  @discardableResult
  private func write(_ contents: String, to url: URL) throws -> URL {
    try FileManager.default.createDirectory(
      at: url.deletingLastPathComponent(), withIntermediateDirectories: true)
    try contents.write(to: url, atomically: true, encoding: .utf8)
    return url
  }

  /// Returns the names of the module archives currently in the shared cache.
  private static func cachedArchives() throws -> [String] {
    try FileManager.default.contentsOfDirectory(atPath: moduleCache.url.path)
      .filter({ (f) in f.hasSuffix(".hylomodule") })
      .map({ (f) in String(f.dropLast(".hylomodule".count)) })
  }

}

/// Returns `true` iff a non-directory file exists at `path`.
private func fileExists(atPath path: String) -> Bool {
  var isDirectory: ObjCBool = true
  let e = FileManager.default.fileExists(atPath: path, isDirectory: &isDirectory)
  return e && !isDirectory.boolValue
}

/// Returns `true` iff a directory exists at `path`.
private func directoryExists(atPath path: String) -> Bool {
  var isDirectory: ObjCBool = false
  let e = FileManager.default.fileExists(atPath: path, isDirectory: &isDirectory)
  return e && isDirectory.boolValue
}

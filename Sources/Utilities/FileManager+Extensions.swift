import Foundation

extension FileManager {

  /// Calls `action` with the URL of a file containing `s`.
  public func withTemporaryFile<T>(containing s: String, _ action: (URL) throws -> T) throws -> T {
    let u = temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: false)
    try s.write(to: u, atomically: true, encoding: .utf8)
    return try action(u)
  }

  /// The URL to the working directory for the current process.
  public var currentDirectoryURL: URL {
    .init(fileURLWithPath: FileManager.default.currentDirectoryPath, isDirectory: true)
  }

  /// Creates a uniquely named temporary directory.
  ///
  /// The caller is responsible for removing the directory, if needed.
  public func createUniqueTemporaryDirectory() throws -> URL {
    let directory = temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
    try createDirectory(at: directory, withIntermediateDirectories: true)
    return directory
  }

  /// Creates an empty temporary directory for the duration of `action`.
  public func withUniqueTemporaryDirectory<T>(_ action: (_ directory: URL) throws -> T) throws -> T {
    let d = try createUniqueTemporaryDirectory()
    defer { try? removeItem(at: d) }
    return try action(d)
  }

  /// Creates an empty temporary directory for the duration of `action`.
  public func withUniqueTemporaryDirectory<T>(_ action: (_ directory: URL) async throws -> T) async throws -> T {
    let d = try createUniqueTemporaryDirectory()
    defer { try? removeItem(at: d) }
    return try await action(d)
  }

}

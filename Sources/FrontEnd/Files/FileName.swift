import Archivist
import Foundation

/// The name of a file.
public enum FileName: Hashable, Sendable {

  /// A local path to a file.
  case local(URL)

  /// A unique identifier for a file that only exists in memory.
  case virtual(Int)

  /// A path to a file whose supplied contents may be different than what is on disk.
  ///
  /// This is needed for LSP support to represent un-saved files.
  case localInMemory(URL)

  /// Returns `true` iff `self` is ordered before `other` in a dictionary.
  public func lexicographicallyPrecedes(_ other: Self) -> Bool {
    // local < localInMemory < virtual

    switch (self, other) {
    //comparison with same types
    case (.local(let a), .local(let b)):
      return a.standardizedFileURL.path().lexicographicallyPrecedes(b.standardizedFileURL.path())
    case (.virtual(let a), .virtual(let b)):
      return a < b
    case (.localInMemory(let a), .localInMemory(let b)):
      return a.standardizedFileURL.path().lexicographicallyPrecedes(b.standardizedFileURL.path())

    // local precedes everything else
    case (.local, _):
      return true
    // localInMemory doesn't precede local but precedes virtual
    case (.localInMemory, .local(_)):
      return false
    case (.localInMemory, .virtual):
      return true
    // virtual is last, doesn't precede anything
    default:
      return false
    }
  }

  /// Returns a textual description of `self`'s path relative to `base`.
  public func gnuPath(relativeTo base: URL) -> String? {
    guard base.isFileURL else { return nil }
    
    let path: URL
    switch self {
    case .local(let p), .localInMemory(let p):
      path = p
    case .virtual:
      return nil
    }
    
    let source = path.standardized.pathComponents
    let prefix = base.standardized.pathComponents

    // Identify the end of the common prefix.
    var i = 0
    while (i != prefix.count) && (i != source.count) && (prefix[i] == source[i]) {
      i += 1
    }

    if (i == source.count) && (i == prefix.count) {
      return "."
    } else {
      var result = Array(repeating: "..", count: prefix.count - i)
      result.append(contentsOf: source[i...])
      return result.joined(separator: "/")
    }
  }

  /// The way in which a file path may be shown.
  public enum PathStyle {

    /// File paths are shown absolute.
    case absolute

    /// File paths are shown relative to a base URL.
    case relative(to: URL)

  }

}

extension FileName: CustomStringConvertible {

  public var description: String {
    switch self {
    case .local(let p):
      return p.relativePath
    case .localInMemory(let p):
      return p.relativePath + "#inmemory"
    case .virtual(let i):
      return "virtual://\(String(UInt(bitPattern: i), radix: 36))"
    }
  }

}

extension FileName: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0:
      self = try .local(.init(string: archive.read(String.self))!)
    case 1:
      self = try .virtual(archive.read(Int.self))
    case 2:
      self = try .localInMemory(.init(string: archive.read(String.self))!)
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .local(let p):
      archive.write(byte: 0)
      try archive.write(p.absoluteString)
    case .virtual(let i):
      archive.write(byte: 1)
      try archive.write(i)
    case .localInMemory(let p):
      archive.write(byte: 2)
      try archive.write(p.absoluteString)
    }
  }

}

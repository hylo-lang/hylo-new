import Archivist
import Foundation

/// The name of a file.
@Archivable
public enum FileName: Hashable, Sendable {

  /// A local path to a file.
  case local(URL)

  /// A unique identifier for a file that only exists in memory.
  ///
  /// The payload can be any URL that uniquely identifies the source file within the Program.
  case virtual(URL)

  /// The associated URL.
  public var url: URL {
    switch self {
    case .local(let url):
      return url
    case .virtual(let url):
      return url
    }
  }

  /// `self` with absolute URLs.
  public var absolute: Self {
    switch self {
    case .local(let url):
      return .local(url.absoluteURL)
    case .virtual(let url):
      return .virtual(url.absoluteURL)
    }
  }
  
  /// Returns `true` iff `self` is ordered before `other` in a dictionary.
  public func lexicographicallyPrecedes(_ other: Self) -> Bool {
    let s = self.url.standardizedFileURL.absoluteString
    let o = other.url.standardizedFileURL.absoluteString
    return s.lexicographicallyPrecedes(o)
  }

  /// Returns the `/`-separated path of `self` relative to `base`, if reachable.
  public func gnuPath(relativeTo base: URL) -> String? {
    let p = self.url
    guard p.scheme == base.scheme,
      p.windowsDriveLetter == base.windowsDriveLetter else { return nil }

    let source = p.standardized.pathComponents
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

extension URL {
  
  /// Returns the drive letter of an absolute file URL on Windows, nil otherwise.
  fileprivate var windowsDriveLetter: Character? {
    #if os(Windows)
      guard
        isFileURL, let firstChar = path.first, firstChar.isLetter,
        path.dropFirst().first == ":"
      else { return nil }

      return Character(firstChar.uppercased())
    #else
      return nil
    #endif
  }

}

extension FileName: CustomStringConvertible {

  public var description: String {
    url.isFileURL ? url.path : url.absoluteString
  }

}

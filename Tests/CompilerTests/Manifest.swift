import Foundation
import Utilities

/// A test manifest.
struct Manifest {

  /// A stage of the compilation pipelne.
  enum Stage: String {

    /// After the abstract syntax tree has been parsed.
    case parsing

    /// After the abstract syntax tree has been typed.
    case typing

    /// After the program has been compiled to binary.
    case codegen

  }

  /// `true` iff `self` requires a standard library.
  private(set) var requiresStandardLibrary: Bool = true

  /// The stage up to which the input should be compiled.
  private(set) var stage: Stage = .codegen

  /// Creates an instance with a default configuration.
  init() {}

  /// Creates an instance parsing the configuration from `options`.
  init<S: Sequence<Substring>>(options: S) throws {
    for s in options {
      try add(option: s)
    }
  }

  /// Returns the manifest of the test case at `root`.
  ///
  /// If `root` is a directory, the manifest is parsed from the contents of a file `package.json`
  /// at the root of this directory. Otherwise, if the first line of the contents of `root` starts
  /// with `"//!"`, the manifest is parsed from the remainder of that line as a list of options,
  /// separated by spaces. Otherwise, a default instance is created.
  ///
  /// An option is either a flag, represented as a character string (e.g., `"no-std"`), or a
  /// key/value pair represented as two strings separated by a colon (e.g, `"stage:typing"`).
  init(contentsOf root: URL) throws {
    // Try to read the actual manifest.
    if root.pathExtension == "package" {
      let json = try Data(contentsOf: root.appendingPathComponent("package.json"))
      self = try JSONDecoder().decode(Manifest.self, from: json)
    }

    // Try to read the manifest's properties from the first line.
    else if let s = Self.firstLine(of: root), s.starts(with: "//!") {
      self = try .init(options: s.split(separator: " ").dropFirst())
    }

    // Return a default manifest.
    else {
      self.init()
    }
  }

  /// Updates the configuration of `self` with the option parsed from `s`.
  private mutating func add<S: StringProtocol>(option s: S) throws {
    let i = s.firstIndex(of: ":") ?? s.endIndex
    let k = s[..<i]
    let v = (i == s.endIndex) ? "" : String(s[s.index(after: i)...])

    switch k {
    case "no-std":
      requiresStandardLibrary = false
    case "stage":
      stage = try Stage(rawValue: v).unwrapOrThrow(ManifestError.invalidStage(v))
    default:
      throw ManifestError.unknownOption
    }
  }

  /// Returns the first line of the file at `url`, which is encoded in UTF-8, or `nil`if that
  /// this file could not be read.
  private static func firstLine(of url: URL) -> Substring? {
    (try? String(contentsOf: url, encoding: .utf8))?.firstLine
  }

}

extension Manifest: Decodable {

  enum Key: String, CodingKey {

    case options

  }

  init(from decoder: any Decoder) throws {
    let c = try decoder.container(keyedBy: Key.self)
    var n = try c.nestedUnkeyedContainer(forKey: .options)
    while !n.isAtEnd {
      try add(option: n.decode(String.self))
    }
  }

}

/// An error that occurred during the parsing of a test manifest.
enum ManifestError: Error {

  /// An invalid option.
  case unknownOption

  /// An invalid stage argument.
  case invalidStage(String)

}

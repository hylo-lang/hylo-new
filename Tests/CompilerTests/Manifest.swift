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
  private(set) var stage: Stage = .typing

  /// Creates an instance with a default configuration.
  init() {}

  /// Creates an instance parsing the configuration from `options`.
  init<S: Sequence<Substring>>(options: S) throws {
    for s in options {
      try add(option: s)
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

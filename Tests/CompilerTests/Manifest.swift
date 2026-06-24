import Foundation
import Utilities

/// A test manifest.
struct Manifest {

  /// A stage of the compilation and testing pipeline.
  enum Stage: String, Comparable {

    /// After the abstract syntax tree has been parsed.
    case parsing

    /// After the abstract syntax tree has been typed.
    case typing

    /// After IR lowering.
    case lowering

    /// After LLVM lowering.
    case llvm

    /// After the program has been compiled and ran.
    case execution

    /// The position of `self` in the pipeline.
    var order: Int {
      switch self {
      case .parsing: 0
      case .typing: 1
      case .lowering: 2
      case .llvm: 3
      case .execution: 4
      }
    }

    /// True iff `l` is earlier in the pipeline than `r`.
    static func < (l: Stage, r: Stage) -> Bool {
      l.order < r.order
    }

  }

  /// The configuration of the optimizer.
  enum Optimizations: String {

    /// No optimization is applied.
    case none

    /// All optimizations are applied
    case all

  }

  /// `true` iff `self` requires a standard library.
  private(set) var requiresStandardLibrary: Bool = true

  /// The stage up to which the input should be compiled.
  private(set) var stage: Stage = .execution

  /// The optimizer configuration with which the input should be compiled.
  private(set) var optimizations: Optimizations = .none

  /// The expected exit status of the input, if executed.
  private(set) var exitStatus: Int32 = 0

  /// The expected textual artifacts of the test run, asserted when present.
  private(set) var artifactExpectations = SortedDictionary<CompilerTests.ArtifactTag, String>()

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

    try self.readArtifactExpectations(forTestAt: root, stage: stage)
  }

  /// Reads and sets expectations for the test case at `root`.
  mutating func readArtifactExpectations(forTestAt root: URL, stage: Stage) throws {
    for tag in CompilerTests.ArtifactTag.allTextual {
      self.artifactExpectations[tag] = try Self.readFromDisk(
        forTestAt: root, tag: tag, minimumStage: tag.minimumStage, stage: stage)
    }
  }

  /// Reads the `tag`-specific expectation for a test case at `root`.
  static func readFromDisk(
    forTestAt root: URL, tag: CompilerTests.ArtifactTag, minimumStage: Manifest.Stage,
    stage: Manifest.Stage
  ) throws -> String? {
    let r = try? String(
      contentsOf: root.deletingPathExtension().appendingPathExtension("\(tag).expected"),
      encoding: .utf8)

    if stage < minimumStage && r != nil {
      throw TestFailure.invalidTestDescription(
        "\(tag) assertion requires stage:\(minimumStage) or higher but was \(stage).")
    }

    return r
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
      stage = try parse(v, for: k, with: Stage.init(rawValue:))
    case "optimizations":
      optimizations = try parse(v, for: k, with: Optimizations.init(rawValue:))
    case "exit-status":
      exitStatus = try parse(v, for: k, with: Int32.init(_:))
    default:
      throw ManifestError.unknownOption
    }
  }

  /// Returns the value of the argument `v` of the option `k`, parsed with `parse`.
  private func parse<T, S: StringProtocol>(
    _ v: String, for k: S, with parse: (String) -> T?
  ) throws -> T {
    try parse(v).unwrapOrThrow(ManifestError.invalidArgument(option: String(k), argument: v))
  }

  /// Returns the first line of the file at `url`, which is encoded in UTF-8, or `nil` if this file
  /// could not be read.
  private static func firstLine(of url: URL) -> Substring? {
    (try? String(contentsOf: url, encoding: .utf8))?.firstLine
  }

  /// A failure reported when parsing a test manifest.
  private enum TestFailure: Error {

    /// The test failed because its description was invalid.
    case invalidTestDescription(String)

    var localizedDescription: String {
      switch self {
      case .invalidTestDescription(let d):
        return "Invalid test description (\(d))"
      }
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

  /// An invalid option argument.
  case invalidArgument(option: String, argument: String)

}

import Archivist

/// A semantic version number.
@Archivable
public struct SemanticVersion: Equatable, Sendable {

  /// The major version component of the semantic version.
  public let major: Int

  /// The minor version component of the semantic version.
  public let minor: Int

  /// The patch version component of the semantic version.
  public let patch: Int

  /// Creates an instance with the given major, minor, and patch components.
  public init(major: Int, minor: Int, patch: Int) {
    self.major = major
    self.minor = minor
    self.patch = patch
  }

  public static func < (lhs: Self, rhs: Self) -> Bool {
    (lhs.major, lhs.minor, lhs.patch) < (rhs.major, rhs.minor, rhs.patch)
  }

}

extension SemanticVersion: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(major).\(minor).\(patch)"
  }

}

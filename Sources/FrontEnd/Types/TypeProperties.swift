/// Properties about the representation of a type.
public struct TypeProperties: Hashable, OptionSet, Sendable {

  /// The raw value of these properties.
  public let rawValue: UInt8

  /// Creates an instance from its raw value.
  public init(rawValue: UInt8) {
    self.rawValue = rawValue
  }

  /// Returns the union of `l` with `r`.
  public static func | (l: Self, r: Self) -> Self {
    l.union(r)
  }

  /// The value contains one or more errors.
  public static let hasError = TypeProperties(rawValue: 1 << 0)

  /// The value contains open variables.
  public static let hasVariable = TypeProperties(rawValue: 1 << 1)

  /// The value contains type aliasess.
  public static let hasAliases = TypeProperties(rawValue: 1 << 2)

}

import Archivist

/// The type of a node in a type tree.
public struct TypeTag: Sendable {

  /// The underlying value of `self`.
  public let value: any TypeTree.Type

  /// Creates an instance with the given underlying value.
  public init(_ value: any TypeTree.Type) {
    self.value = value
  }

  /// Returns `true` iff `scrutinee` and `pattern` denote the same node type.
  public static func ~= (pattern: any TypeTree.Type, scrutinee: Self) -> Bool {
    scrutinee == pattern
  }

  /// Returns `true` iff `l` and `r` denote the same node type.
  public static func == (l: Self, r: any TypeTree.Type) -> Bool {
    l.value == r
  }

  /// Returns `true` iff `l` and `r` denote a different node type.
  public static func != (l: Self, r: any TypeTree.Type) -> Bool {
    l.value != r
  }

  static let allValues: [any TypeTree.Type] = [
    Arrow.self,
    AssociatedType.self,
    Bundle.self,
    EqualityWitness.self,
    Enum.self,
    ErrorType.self,
    GenericParameter.self,
    Implication.self,
    LiteralType.self,
    MachineType.self,
    Metakind.self,
    Metatype.self,
    Namespace.self,
    OpaqueType.self,
    RemoteType.self,
    Struct.self,
    Trait.self,
    Tuple.self,
    TypeAlias.self,
    TypeApplication.self,
    TypeVariable.self,
    UniversalType.self,
  ]

  static let indices = Dictionary(
    uniqueKeysWithValues: allValues.enumerated().map({ (i, k) in (TypeTag(k), i) }))

}

extension TypeTag: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.value == r.value
  }

}

extension TypeTag: Hashable {

  public func hash(into hasher: inout Hasher) {
    hasher.combine(ObjectIdentifier(value))
  }

}

extension TypeTag: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try .init(Self.allValues[Int(archive.readUnsignedLEB128())])
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    archive.write(unsignedLEB128: Self.indices[self]!)
  }

}

extension TypeTag: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}

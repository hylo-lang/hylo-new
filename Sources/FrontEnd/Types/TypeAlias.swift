import Archivist

/// A type alias.
@Archivable
public struct TypeAlias: TypeTree {

  /// The declaration introducing this type.
  public let declaration: TypeAliasDeclaration.ID

  /// The aliased type.
  public let aliasee: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(declaration: TypeAliasDeclaration.ID, aliasee: AnyTypeIdentity) {
    self.declaration = declaration
    self.aliasee = aliasee
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    .hasAliases
  }

}

extension TypeAlias: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.program[declaration].identifier.value
  }

}

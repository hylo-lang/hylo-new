import Archivist

/// A nominal sum type.
@Archivable
public struct Enum: TypeTree {

  /// The declaration introducing this type.
  public let declaration: EnumDeclaration.ID

  /// Creates an instance with the given properties.
  public init(declaration: EnumDeclaration.ID) {
    self.declaration = declaration
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension Enum: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.program[declaration].identifier.value
  }

}

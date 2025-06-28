import Archivist

/// A trait.
@Archivable
public struct Trait: TypeTree {

  /// The declaration introducing this type.
  public let declaration: TraitDeclaration.ID

  /// Creates an instance with the given properties.
  public init(declaration: TraitDeclaration.ID) {
    self.declaration = declaration
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension Trait: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.program[declaration].identifier.value
  }

}

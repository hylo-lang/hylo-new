import Archivist

/// The selection of the associated type of some type.
@Archivable
public struct AssociatedType: TypeTree {

  /// The declaration of the type.
  public let declaration: AssociatedTypeDeclaration.ID

  /// The qualification of the type.
  public let qualification: WitnessExpression

  /// Creates an instance with the given properties.
  public init(declaration: AssociatedTypeDeclaration.ID, qualification: WitnessExpression) {
    self.declaration = declaration
    self.qualification = qualification
  }

  /// Properties about `self` and its children.
  public var properties: TypeProperties {
    qualification.type.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AssociatedType {
    .init(declaration: declaration, qualification: store.map(qualification, transform))
  }

}

extension AssociatedType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let n = printer.program[declaration].identifier.value
    if printer.configuration.useVerboseTypes {
      return "\(printer.show(qualification)).\(n)"
    } else {
      let (c, a) = printer.program.types.seenAsTraitApplication(qualification.type)!
      let m = printer.program[printer.program.types[c].declaration].identifier.value
      return "(\(printer.show(a.values[0]))::\(m)).\(n)"
    }
  }

}

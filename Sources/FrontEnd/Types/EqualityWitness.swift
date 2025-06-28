/// The type of a context parameter witnessing the equality of two types.
public struct EqualityWitness: TypeTree {

  /// The left-hand side of the equality.
  public let lhs: AnyTypeIdentity

  /// The right-hand side of the equality.
  public let rhs: AnyTypeIdentity

  /// Properties about `self`.
  public var properties: TypeProperties {
    lhs.properties | rhs.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> EqualityWitness {
    .init(lhs: store.map(lhs, transform), rhs: store.map(rhs, transform))
  }

}

extension EqualityWitness: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "(\(printer.show(lhs)) ~ \(printer.show(rhs)))"
  }

}

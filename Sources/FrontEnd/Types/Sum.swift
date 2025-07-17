import Archivist

/// A tagged union of types.
@Archivable
public struct Sum: TypeTree {

  /// The left-hand side of the sum.
  public let lhs: AnyTypeIdentity

  /// The right-hand side of the sum.
  public let rhs: AnyTypeIdentity

  /// Creates an instance representing the sum of `lhs` and `rhs`.
  public init(_ lhs: AnyTypeIdentity, _ rhs: AnyTypeIdentity) {
    self.lhs = lhs
    self.rhs = rhs
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    lhs.properties.union(rhs.properties)
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Sum {
    .init(store.map(lhs, transform), store.map(rhs, transform))
  }

}

extension Sum: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(lhs)) + \(printer.show(rhs))"
  }

}

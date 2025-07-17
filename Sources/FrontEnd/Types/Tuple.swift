import Archivist
import Utilities

/// The type of a tuple.
@Archivable
public struct Tuple: TypeTree {

  /// The left-hand side of the product.
  public let lhs: AnyTypeIdentity

  /// The right-hand side of the product.
  public let rhs: AnyTypeIdentity

  /// Creates an instance representing the product of `lhs` and `rhs`.
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
  ) -> Tuple {
    .init(store.map(lhs, transform), store.map(rhs, transform))
  }

}

extension Tuple: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(lhs)) * \(printer.show(rhs))"
  }

}

import Archivist
import Utilities

/// The type of a function or subscript bundle.
@Archivable
public struct Bundle: TypeTree {

  /// The common shape of the types of the variants in the bundle.
  public let shape: AnyTypeIdentity

  /// The effects of the variants in the bundle.
  public let variants: AccessEffectSet

  /// Creates an instance with the given properties.
  public init(shape: AnyTypeIdentity, variants: AccessEffectSet) {
    self.shape = shape
    self.variants = variants
  }

  /// Properties about `self` and its children.
  public var properties: TypeProperties {
    shape.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Bundle {
    .init(shape: store.map(shape, transform), variants: variants)
  }

}

extension Bundle: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(shape)) { \(list: variants) }"
  }

}

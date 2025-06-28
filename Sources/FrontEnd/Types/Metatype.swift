import Archivist

/// The type of a type expression.
@Archivable
public struct Metatype: TypeTree {

  /// The type of which `self` is the type.
  public let inhabitant: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(inhabitant: AnyTypeIdentity) {
    self.inhabitant = inhabitant
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    inhabitant.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Metatype {
    .init(inhabitant: store.map(inhabitant, transform))
  }

}

extension Metatype: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "Metatype<\(printer.show(inhabitant))>"
  }

}

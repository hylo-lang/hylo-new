import Archivist

/// A tagged union of types.
@Archivable
public struct Sum: TypeTree {

  /// The elements of the union.
  public let elements: [AnyTypeIdentity]

  /// Creates an instance with the given properties.
  public init(elements: [AnyTypeIdentity]) {
    self.elements = elements
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    elements.reduce([], { (a, e) in a.union(e.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Sum {
    .init(elements: elements.map({ (e) in store.map(e, transform) }))
  }

}

extension Sum: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    elements.isEmpty ? "Never" : "(\(printer.show(elements, separatedBy: " (+) ")))"
  }

}

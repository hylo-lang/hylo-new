import Archivist
import Utilities

/// The type of an implicit abstraction.
@Archivable
public struct Implication: TypeTree {

  /// The left-hand side of the implication, which is not empty.
  public let usings: [AnyTypeIdentity]

  /// The right-hand side of the implication.
  public let body: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(context: [AnyTypeIdentity], head: AnyTypeIdentity) {
    assert(!context.isEmpty)
    self.usings = context
    self.body = head
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    usings.reduce(body.properties, { (a, i) in a.union(i.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Implication {
    .init(
      context: usings.map({ (t) in store.map(t, transform) }),
      head: store.map(body, transform))
  }

}

extension Implication: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let t = usings.uniqueElement {
      return "\(printer.show(t)) ==> \(printer.show(body))"
    } else {
      return "(\(printer.show(usings))) ==> \(printer.show(body))"
    }
  }

}

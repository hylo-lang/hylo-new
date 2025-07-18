import Archivist
import Utilities

/// The type of a tuple.
@Archivable
public enum Tuple: TypeTree {

  /// The first element of the tuple followed by the rest.
  case cons(head: AnyTypeIdentity, tail: AnyTypeIdentity)

  /// An empty tuple.
  case empty

  /// Properties about `self`.
  public var properties: TypeProperties {
    switch self {
    case .cons(let head, let tail):
      return head.properties.union(tail.properties)
    case .empty:
      return .init()
    }
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Tuple {
    switch self {
    case .cons(let head, let tail):
      return .cons(head: store.map(head, transform), tail: store.map(tail, transform))
    case .empty:
      return .empty
    }

  }

}

extension Tuple: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    guard case .cons(let head, let tail) = self else { return "Void" }

    var elements = [head]
    var rest = tail
    while let t = printer.program.types.cast(rest, to: Tuple.self) {
      switch printer.program.types[t] {
      case .cons(let a, let b):
        elements.append(a)
        rest = b
      case .empty:
        return "{\(printer.show(elements))}"
      }
    }

    return "{\(printer.show(elements)), ...\(printer.show(rest))}"
  }

}

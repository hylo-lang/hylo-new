import Archivist
import OrderedCollections
import Utilities

/// The application of a type abstraction.
@Archivable
public struct TypeApplication: TypeTree {

  /// The abstraction being applied.
  public var abstraction: AnyTypeIdentity

  /// The arguments of the application.
  public var arguments: TypeArguments

  /// Properties about `self`.
  public var properties: TypeProperties {
    arguments.values.reduce(abstraction.properties, { (a, i) in a.union(i.properties) })
  }

  /// Creates an instance with the given properties.
  public init(abstraction: AnyTypeIdentity, arguments: TypeArguments) {
    self.abstraction = abstraction
    self.arguments = arguments
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> TypeApplication {
    let t = store.map(abstraction, transform)
    let x = arguments.mapValues({ (a) in store.map(a, transform) })
    return .init(abstraction: t, arguments: x)
  }

}

extension TypeApplication: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(abstraction))<\(printer.show(arguments.values))>"
  }

}

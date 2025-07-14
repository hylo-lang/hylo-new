import Archivist

/// A pointer to a monomorphic free function.
///
/// Function pointers denote addresses of a non-generic functions having empty environments, e.g.,
/// instances of `[]() let -> Int`. They can be used to implement low-level dynamic dispatch
/// mechanisms, e.g., to pass a callback across a language boundary.
@Archivable
public struct FunctionPointer: TypeTree {

  /// The input types of the pointee.
  public let inputs: [AnyTypeIdentity]

  /// The output type of the pointee.
  public let output: AnyTypeIdentity

  /// Creates an instance with the givenproperties.
  public init(inputs: [AnyTypeIdentity], output: AnyTypeIdentity) {
    self.inputs = inputs
    self.output = output
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    inputs.reduce(output.properties, { (a, i) in a.union(i.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> FunctionPointer {
    .init(
      inputs: inputs.map({ (i) in store.map(i, transform) }),
      output: store.map(output, transform))
  }

}

extension FunctionPointer: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "FunctionPointer<(\(printer.show(inputs))) -> \(printer.show(output))>"
  }

}

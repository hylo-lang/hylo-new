import Archivist

/// The type of a type witness.
///
/// A type witness is a run-time representation of a type, typically used to substitute generic
/// type parameters in existentialized functions.
@Archivable
public struct TypeWitness: TypeTree {

  /// Creates an instance.
  public init() {}

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension TypeWitness: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "Type"
  }

}

/// The type of a kind expression.
public struct Metakind: TypeTree {

  /// The kind of which `self` is the type.
  public let inhabitant: Kind

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension Metakind: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    inhabitant.description
  }

}

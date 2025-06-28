/// A unification variable in a type tree.
public struct TypeVariable: TypeTree {

  /// The identifier of the variable.
  public let identifier: Int

  /// Properties about `self`.
  public var properties: TypeProperties {
    .hasVariable
  }

}

extension TypeVariable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "%\(String(identifier, radix: 36))"
  }

}

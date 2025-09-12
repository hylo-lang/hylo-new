import Archivist

/// The expression of a tuple type.
@Archivable
public struct TupleTypeExpression: Expression {

  /// The types of the elements.
  public let elements: [ExpressionIdentity]

  /// The ellipsis before the last element, if any.
  ///
  /// - Invariant: If this property is not `nit`, then `self.elements.count >= 2`.
  public let ellipsis: Token?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(elements: [ExpressionIdentity], ellipsis: Token?, site: SourceSpan) {
    assert(ellipsis == nil || elements.count >= 2)
    self.elements = elements
    self.ellipsis = ellipsis
    self.site = site
  }

}

extension TupleTypeExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if ellipsis != nil {
      return "{\(printer.show(elements.dropLast())), ...\(printer.show(elements.last!))}"
    } else {
      return "{\(printer.show(elements))}"
    }
  }

}

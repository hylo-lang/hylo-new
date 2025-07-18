import Archivist

/// The expression of a tuple literal.
@Archivable
public struct TupleLiteral: Expression {

  /// The elements of the tuple.
  public let elements: [ExpressionIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(elements: [ExpressionIdentity], site: SourceSpan) {
    self.elements = elements
    self.site = site
  }

}

extension TupleLiteral: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if elements.count == 1 {
      return "(\(printer.show(elements)),)"
    } else {
      return "(\(printer.show(elements)))"
    }
  }

}

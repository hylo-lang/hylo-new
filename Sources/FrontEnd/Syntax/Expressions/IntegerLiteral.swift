import Archivist

/// The expression of an integer literal.
@Archivable
public struct IntegerLiteral: LiteralExpression {

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(site: SourceSpan) {
    self.site = site
  }

  /// The value of the literal.
  public var value: Substring { site.text }

  public static let literalType: LiteralType = .integer

}

extension IntegerLiteral: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    value.description
  }

}

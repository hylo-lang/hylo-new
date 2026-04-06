import Archivist

/// A yield statement.
@Archivable
public struct Yield: Statement {

  /// The introducer of this statement, if any.
  public let introducer: Token?

  /// The yielded value.
  public let value: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(introducer: Token?, value: ExpressionIdentity, site: SourceSpan) {
    self.introducer = introducer
    self.value = value
    self.site = site
  }

}

extension Yield: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "yield \(printer.show(value))"
  }

}

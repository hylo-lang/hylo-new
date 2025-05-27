import Archivist

/// A return statement.
@Archivable
public struct Return: Statement {

  /// The introducer of this statement, if any.
  public let introducer: Token?

  /// The return value, if any.
  public let value: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(introducer: Token?, value: ExpressionIdentity?, site: SourceSpan) {
    self.introducer = introducer
    self.value = value
    self.site = site
  }

}

extension Return: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let v = value {
      return "return \(printer.show(v))"
    } else {
      return "return"
    }
  }

}

import Archivist

/// A while statement.
@Archivable
public struct While: Statement {

  /// The introducer of this statement.
  public let introducer: Token

  /// The condition of the loop.
  ///
  /// - Requires `condition.count > 0`.
  public let conditions: [ConditionIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// The body of the loop: `{ ... }`.
  public let body: Block.ID

  /// Creates an instance with the given properties.
  public init(introducer: Token, condition: [ConditionIdentity], body: Block.ID, site: SourceSpan) {
    self.introducer = introducer
    self.conditions = condition
    self.body = body
    self.site = site
  }

}

extension While: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "while \(printer.show(conditions)) \(printer.show(body))"
  }

}

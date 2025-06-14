import Archivist

/// A pattern matching expression.
@Archivable
public struct PatternMatch: Expression {

  /// The introducer of this expression.
  public let introducer: Token

  /// The expression being compared with each pattern.
  public let scrutinee: ExpressionIdentity

  /// The cases of the expression.
  public let branches: [PatternMatchCase.ID]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Token,
    scrutinee: ExpressionIdentity,
    branches: [PatternMatchCase.ID],
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.scrutinee = scrutinee
    self.branches = branches
    self.site = site
  }

}

extension PatternMatch: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "match \(printer.show(scrutinee)) {\n"
    for b in branches { result.append(printer.show(b).indented + "\n") }
    result.append("}")
    return result
  }

}

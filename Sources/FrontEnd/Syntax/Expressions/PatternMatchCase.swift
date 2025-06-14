import Archivist

/// A case in a pattern matching expression.
@Archivable
public struct PatternMatchCase: Expression, Scope {

  /// The introducer of this case.
  public let introducer: Token

  /// The expression being compared with each pattern.
  public let pattern: PatternIdentity

  /// The body of the case.
  public let body: [StatementIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Token,
    pattern: PatternIdentity,
    body: [StatementIdentity],
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.pattern = pattern
    self.body = body
    self.site = site
  }

}

extension PatternMatchCase: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "case "

    if printer.program.isExpression(pattern) {
      result.append("(\(printer.show(pattern)))")
    } else {
      result.append(printer.show(pattern))
    }

    result.append(" {\n")
    for s in body { result.append(printer.show(s).indented + "\n") }
    result.append("}")

    return result
  }

}

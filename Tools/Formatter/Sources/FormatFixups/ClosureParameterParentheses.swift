import SwiftSyntax

/// A rewriter that parenthesizes the parameter lists of closures naming at least one parameter,
/// e.g. rewriting `{ e in ... }` as `{ (e) in ... }`.
///
/// Closures whose parameters are all anonymous (e.g. `{ _ in ... }`) are left unchanged.
public final class ClosureParameterParentheses: SyntaxRewriter {

  /// Creates an instance.
  public override init(viewMode: SyntaxTreeViewMode = .sourceAccurate) {
    super.init(viewMode: viewMode)
  }

  public override func visit(_ node: ClosureSignatureSyntax) -> ClosureSignatureSyntax {
    var transformed = super.visit(node)
    guard
      case .simpleInput(let names) = transformed.parameterClause,
      names.contains(where: { (p) in p.name.tokenKind != .wildcard })
    else { return transformed }
    transformed.parameterClause = .parameterClause(parenthesized(names))
    return transformed
  }

  /// Returns `names` wrapped in parentheses, moving the trivia surrounding the list onto them.
  private func parenthesized(
    _ names: ClosureShorthandParameterListSyntax
  ) -> ClosureParameterClauseSyntax {
    var parameters: [ClosureParameterSyntax] = []
    for (i, n) in names.enumerated() {
      var p = n
      if i == 0 { p.leadingTrivia = Trivia() }
      if i == names.count - 1 { p.trailingTrivia = Trivia() }
      parameters.append(ClosureParameterSyntax(firstName: p.name, trailingComma: p.trailingComma))
    }
    return ClosureParameterClauseSyntax(
      leadingTrivia: names.first!.leadingTrivia,
      leftParen: .leftParenToken(),
      parameters: ClosureParameterListSyntax(parameters),
      rightParen: .rightParenToken(),
      trailingTrivia: names.last!.trailingTrivia)
  }

}

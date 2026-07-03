import SwiftParser
import SwiftSyntax

/// Returns `source` rewritten to follow the Hylo formatting conventions that `swift-format`
/// cannot express:
///
/// - a blank line after the opening brace and before the closing brace of the multiline body of a
///   type, extension, or protocol declaration;
/// - parentheses around the parameters of closures naming at least one parameter.
///
/// Returns `source` unchanged if it does not parse without errors, or if the rewrite would
/// introduce a parse error.
public func applyingConventionFixups(to source: String) -> String {
  let tree = Parser.parse(source: source)
  if tree.hasError { return source }

  var transformed = Syntax(TypeBodyBlankLines().rewrite(tree))
  transformed = ClosureParameterParentheses().rewrite(transformed)

  let result = transformed.description
  return Parser.parse(source: result).hasError ? source : result
}

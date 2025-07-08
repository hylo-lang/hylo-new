import Archivist

/// The declaration of a variant in a function or subscript bundle.
@Archivable
public struct VariantDeclaration: Declaration, Scope {

  /// The effect of the variant on its receiver operator.
  public let effect: Parsed<AccessEffect>

  /// The body of the variant.
  public let body: [StatementIdentity]?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    effect: Parsed<AccessEffect>,
    body: [StatementIdentity]?,
    site: SourceSpan
  ) {
    self.effect = effect
    self.body = body
    self.site = site
  }

}

extension VariantDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "\(effect)"
    if let b = body {
      result.append(" {\n")
      for s in b { result.append(printer.show(s).indented + "\n") }
      result.append("}")
    }
    return result
  }

}

import Archivist
import Utilities

/// The declaration of a type alias.
@Archivable
public struct TypeAliasDeclaration: TypeDeclaration, ModifiableDeclaration, Scope {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared alias.
  public let identifier: Parsed<String>

  /// The type parameters of the struct.
  public let parameters: [GenericParameterDeclaration.ID]

  /// The expression of the aliased type.
  public let aliasee: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Token,
    identifier: Parsed<String>,
    parameters: [GenericParameterDeclaration.ID],
    aliasee: ExpressionIdentity,
    site: SourceSpan
  ) {
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.parameters = parameters
    self.aliasee = aliasee
    self.site = site
  }

}

extension TypeAliasDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("type \(identifier.value) = \(printer.show(aliasee))")

    if !parameters.isEmpty {
      result.append("<\(printer.show(parameters))>")
    }

    return result
  }

}

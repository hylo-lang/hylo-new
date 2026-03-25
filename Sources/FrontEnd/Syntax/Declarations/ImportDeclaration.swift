import Archivist

/// The declaration of a module import.
@Archivable
public struct ImportDeclaration: Declaration {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The identifier of the imported module.
  public let identifier: Parsed<String>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Token,
    identifier: Parsed<String>,
    site: SourceSpan
  ) {
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.site = site
  }

}

extension ImportDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "import \(identifier.value)"
  }

}

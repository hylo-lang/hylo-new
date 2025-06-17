import Archivist

/// The declaration of a type extension.
@Archivable
public struct ExtensionDeclaration: TypeExtendingDeclaration {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The type parameters and usings of the extension.
  public let contextParameters: ContextParameters

  /// The type being extended.
  public let extendee: ExpressionIdentity

  /// The members of the extension.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Token,
    contextParameters: ContextParameters,
    extendee: ExpressionIdentity,
    members: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.contextParameters = contextParameters
    self.extendee = extendee
    self.members = members
    self.site = site
  }

}

extension ExtensionDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let e = printer.show(extendee)
    let w = contextParameters.isEmpty ? "" : " \(printer.show(contextParameters))"
    let m = members.map({ (m) in printer.show(m).indented }).joined(separator: "\n")
    return """
      extension\(w) \(e) {
      \(m)
      }
      """
  }

}

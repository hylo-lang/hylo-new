import Archivist

/// The declaration of an associated type.
@Archivable
public struct AssociatedTypeDeclaration: TypeDeclaration {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared associated type.
  public let identifier: Parsed<String>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(introducer: Token, identifier: Parsed<String>, site: SourceSpan) {
    self.introducer = introducer
    self.identifier = identifier
    self.site = site
  }

}

extension AssociatedTypeDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "type \(identifier.value)"
  }

}

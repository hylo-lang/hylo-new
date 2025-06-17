import Archivist
import Utilities

/// The declaration of a type alias.
public struct TypeAliasDeclaration: TypeDeclaration, ModifiableDeclaration, Scope {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared alias.
  public let identifier: Parsed<String>

  /// The expression of the aliased type.
  public let aliasee: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension TypeAliasDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("type \(identifier.value) = \(printer.show(aliasee))")
    return result
  }

}

extension TypeAliasDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.modifiers = try archive.read([Parsed<DeclarationModifier>].self, in: &context)
    self.introducer = try archive.read(Token.self, in: &context)
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.aliasee = try archive.read(ExpressionIdentity.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(modifiers, in: &context)
    try archive.write(introducer, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(aliasee, in: &context)
    try archive.write(site, in: &context)
  }

}

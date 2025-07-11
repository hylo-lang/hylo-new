import Archivist

/// The declaration of a structure.
@Archivable
public struct StructDeclaration: TypeDeclaration, ModifiableDeclaration, Annotatable, Scope {

  /// The annotations on this declaration.
  public let annotations: [Annotation]

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared struct.
  public let identifier: Parsed<String>

  /// The type parameters of the struct.
  public let parameters: [GenericParameterDeclaration.ID]

  /// The conformances declared along with the struct.
  public let conformances: [ConformanceDeclaration.ID]

  /// The members of the declared struct.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    annotations: [Annotation],
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Token,
    identifier: Parsed<String>,
    parameters: [GenericParameterDeclaration.ID],
    conformances: [ConformanceDeclaration.ID],
    members: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.annotations = annotations
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.parameters = parameters
    self.conformances = conformances
    self.members = members
    self.site = site
  }

}

extension StructDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("struct \(identifier.value)")

    if !parameters.isEmpty {
      result.append("<\(printer.show(parameters))>")
    }

    if !conformances.isEmpty {
      result.append(" is \(printer.show(adjunct: conformances))")
    }

    result.append(" {\n")
    for m in members { result.append(printer.show(m).indented + "\n") }
    result.append("}")

    return result
  }

}

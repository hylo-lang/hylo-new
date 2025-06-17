import Archivist

/// The declaration of a conformance of a type to a trait.
@Archivable
public struct ConformanceDeclaration: TypeExtendingDeclaration {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  ///
  /// This token is a `given` keyword if the conformance is declared on its own, or a colon if it
  /// is "adjunct" to a struct. In the latter case, the conformance declaration has no parameters
  /// and no members; those belong to the struct declaration.
  public let introducer: Token

  /// The compile-time parameters of the conformance.
  public let staticParameters: ContextParameters

  /// The expression of the witness defined by the declaration.
  public let witness: StaticCall.ID

  /// The members of the declaration.
  public let members: [DeclarationIdentity]?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Token,
    staticParameters: ContextParameters,
    witness: StaticCall.ID,
    members: [DeclarationIdentity]?,
    site: SourceSpan
  ) {
    self.modifiers = modifiers
    self.introducer = introducer
    self.staticParameters = staticParameters
    self.witness = witness
    self.members = members
    self.site = site
  }

  /// Returns `true` iff `self` is adjunct to a type declaration.
  public var isAdjunct: Bool {
    introducer.text == "is"
  }

}

extension ConformanceDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let sugared = printer.program.seenAsConformanceTypeExpression(witness)!

    var result = "given"
    if !staticParameters.isEmpty {
      result.append(" " + printer.show(staticParameters))
    }

    result.append(" \(printer.show(sugared.conformer)) is \(printer.show(sugared.concept))")
    if !sugared.arguments.isEmpty {
      result.append("<\(printer.show(sugared.arguments))>")
    }

    if let b = members {
      result.append(" {\n")
      for m in b { result.append(printer.show(m).indented + "\n") }
      result.append("}")
    }

    return result
  }

}

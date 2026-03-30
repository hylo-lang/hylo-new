/// A declaration that may have modifiers.
public protocol ModifiableDeclaration: Declaration {

  /// The modifiers applied to this declaration.
  var modifiers: [Parsed<DeclarationModifier>] { get }

}

extension ModifiableDeclaration {

  /// Returns `true` iff `self` has the given declaration modifier.
  public func `is`(_ m: DeclarationModifier) -> Bool {
    modifiers.contains(where: { (x) in x.value == m })
  }

  /// Returns the span of the given declaration modifier, if present.
  public func spanForModifier(_ m: DeclarationModifier) -> SourceSpan? {
    modifiers.first(where: { (x) in x.value == m })?.site
  }

}

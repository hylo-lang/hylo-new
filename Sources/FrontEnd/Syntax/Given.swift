/// The declaration of a given.
public enum Given: Hashable, Sendable {

  /// A user-defined given.
  case user(DeclarationIdentity)

  /// The built-in given of a coercion.
  case coercion(EqualityProperty)

  /// A given defining the conformance of `P.Self` to `P` in the declaration of `P`.
  case recursive(AnyTypeIdentity)

  /// A given that is assumed during implicit resolution.
  case assumed(Int, AnyTypeIdentity)

  /// A given nested in a trait.
  indirect case nested(TraitDeclaration.ID, Given)

  /// Returns `true` iff `self` is `.recursive`.
  public var isSelfRecursive: Bool {
    if case .recursive = self { true } else { false }
  }

}

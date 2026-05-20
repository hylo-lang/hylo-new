/// The declarations of the requirements of a trait.
public struct TraitRequirements {

  /// Associated type requirements.
  public let types: [AssociatedTypeDeclaration.ID]

  /// Associated conformance requirements.
  public let conformances: [ConformanceDeclaration.ID]

  /// Member function and subscript requirements.
  public let members: [DeclarationIdentity]

}

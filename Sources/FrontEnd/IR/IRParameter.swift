/// A parameter in a Hylo IR function.
public struct IRParameter: Sendable {

  /// The type of the parameter.
  public let type: AnyTypeIdentity

  /// The capabilities of the parameter.
  public let access: AccessEffect

  /// The declaration of the parameter, if any.
  public let declaration: DeclarationIdentity?

  /// Creates an instance with the given properties.
  public init(type: AnyTypeIdentity, access: AccessEffect, declaration: DeclarationIdentity?) {
    assert(!type[.hasAliases])
    self.type = type
    self.access = access
    self.declaration = declaration
  }

}

/// A parameter in a Hylo IR function.
public struct IRParameter: Sendable {

  /// The type of the parameter.
  public let type: IRType

  /// The capabilities of the parameter.
  public let access: AccessEffect

  /// The declaration of the parameter, if any.
  public let declaration: DeclarationIdentity?

}

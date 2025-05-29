/// The declaration of a callable entity.
public protocol RoutineDeclaration: ModifiableDeclaration {

  /// The compile-time parameters of the entity.
  var staticParameters: ContextParameters { get }

  /// The run-time parameters of the entity.
  var parameters: [ParameterDeclaration.ID] { get }

  /// The effect of the entity's call operator.
  var effect: Parsed<AccessEffect> { get }

  /// The type of the value produced by an application of the entity.
  var output: ExpressionIdentity? { get }

}

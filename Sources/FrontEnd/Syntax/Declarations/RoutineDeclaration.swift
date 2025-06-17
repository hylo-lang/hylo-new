/// The declaration of a callable entity.
public protocol RoutineDeclaration: ModifiableDeclaration {

  /// The type parameters and usings of the entity.
  var contextParameters: ContextParameters { get }

  /// The capture-list of the entity.
  var captures: CaptureList { get }

  /// The run-time parameters of the entity.
  var parameters: [ParameterDeclaration.ID] { get }

  /// The effect of the entity's call operator.
  var effect: Parsed<AccessEffect> { get }

  /// The type of the value produced by an application of the entity.
  var output: ExpressionIdentity? { get }

}

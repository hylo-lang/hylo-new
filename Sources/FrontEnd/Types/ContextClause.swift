/// The context parameters of a type abstraction.
public struct ContextClause {

  /// The variables introduced by the context clause.
  public let parameters: [GenericParameter.ID]

  /// The types of the context parameters.
  public let usings: [AnyTypeIdentity]

  /// `true` iff `self` doesn't contain any parameter.
  public var isEmpty: Bool {
    parameters.isEmpty && usings.isEmpty
  }

  /// An empty clause.
  public static var empty: ContextClause {
    .init(parameters: [], usings: [])
  }

}

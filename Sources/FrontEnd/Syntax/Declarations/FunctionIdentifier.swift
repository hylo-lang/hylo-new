import Archivist

/// The identifier of a function.
@Archivable
public enum FunctionIdentifier: Equatable, Sendable {

  /// A simple identifier.
  case simple(String)

  /// An operator with its notation.
  case `operator`(OperatorNotation, String)

  /// A lambda.
  case lambda

}

extension FunctionIdentifier: CustomStringConvertible {

  public var description: String {
    switch self {
    case .simple(let s):
      return s
    case .operator(let n, let s):
      return "\(n)\(s)"
    case .lambda:
      return ""
    }
  }

}

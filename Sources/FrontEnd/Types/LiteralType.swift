import Archivist

/// The type of a literal expression.
@Archivable
public enum LiteralType: TypeTree {

  /// An integer literal.
  case integer

  /// A floating point literal.
  case float

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension LiteralType: CustomStringConvertible {

  public var description: String {
    switch self {
    case .integer:
      return "IntegerLiteral"
    case .float:
      return "FloatingPointerLiteral"
    }
  }

}

extension LiteralType: LosslessStringConvertible {

  public init?<S: StringProtocol>(_ description: S) {
    switch description {
    case "IntegerLiteral":
      self = .integer
    case "FloatingPointerLiteral":
      self = .float
    default:
      return nil
    }
  }

}

extension LiteralType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    self.description
  }

}

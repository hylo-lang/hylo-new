import Archivist

/// The expression of an explicit conversion.
@Archivable
public struct Conversion: Expression {

  /// A conversion operator.
  @Archivable
  public enum Operator: UInt8, Sendable {

    /// A guaranteed conversion into a type that can represent the source.
    case up

    /// A forced conversion unto a type that may represent the source.
    case down

    /// A built-in conversion to a pointer.
    case pointer

  }

  /// The value being converted.
  public let source: ExpressionIdentity

  /// The type to which the value is converted.
  public let target: ExpressionIdentity

  /// The semantics of the conversion.
  ///
  /// Parsed from the `as`/`as!`/`as*` operators.
  public let semantics: Parsed<Operator>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    source: ExpressionIdentity,
    target: ExpressionIdentity,
    semantics: Parsed<Operator>,
    site: SourceSpan
  ) {
    self.source = source
    self.target = target
    self.semantics = semantics
    self.site = site
  }

}

extension Conversion: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(source)) \(semantics.value) \(printer.show(target))"
  }

}

extension Conversion.Operator: LosslessStringConvertible {

  public init?<T: StringProtocol>(_ description: T) {
    switch description {
    case "as": self = .up
    case "as!": self = .down
    case "as*": self = .pointer
    default: return nil
    }
  }

  public var description: String {
    switch self {
    case .up: return "as"
    case .down: return "as!"
    case .pointer: return "as*"
    }
  }

}

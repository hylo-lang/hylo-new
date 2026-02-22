import Archivist

/// A pattern introducing a (possibly empty) set of bindings.
@Archivable
public struct BindingPattern: Pattern {

  /// The introducer of a binding pattern.
  @Archivable
  public enum Introducer: UInt8, Sendable {

    case `let`, `set`, `var`, `inout`, sinklet

  }

  /// The introducer of this declaration.
  public let introducer: Parsed<Introducer>

  /// A tree containing the declarations of the bindings being introduced.
  public let pattern: PatternIdentity

  /// The type ascription of the parameter.
  public let ascription: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Parsed<Introducer>,
    pattern: PatternIdentity,
    ascription: ExpressionIdentity?,
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.pattern = pattern
    self.ascription = ascription
    self.site = site
  }

  /// Returns `true` iff `self` introduces stored bindings.
  public var introducesStoredBindings: Bool {
    (introducer.value == .var) || (introducer.value == .sinklet)
  }

}

extension BindingPattern: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "\(introducer) \(printer.show(pattern))"

    if let a = ascription {
      result.append(": \(printer.show(a))")
    } else if let t = printer.program[pattern.module].type(assignedTo: pattern) {
      result.append(": \(printer.show(t))")
    }

    return result
  }

}

extension BindingPattern.Introducer: CustomStringConvertible {

  public var description: String {
    switch self {
    case .let:
      return "let"
    case .set:
      return "set"
    case .var:
      return "var"
    case .inout:
      return "inout"
    case .sinklet:
      return "sink let"
    }
  }

}

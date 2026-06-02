import Archivist

/// A conditional-compilation statement.
@Archivable
public struct ConditionalCompilation: Equatable, Statement {

  /// A comparison test for semantic version.
  @Archivable
  public enum VersionComparison: Equatable, Sendable {

    /// Represents "_ >= payload".
    case greaterOrEqual(SemanticVersion)

    /// Represents "_ < payload".
    case less(SemanticVersion)

    /// Evaluate the comparison predicate for `lhs`.
    func evaluate(for lhs: SemanticVersion) -> Bool {
      switch self {
      case .greaterOrEqual(let target):
        return !(lhs < target)
      case .less(let target):
        return lhs < target
      }
    }

  }

  /// A condition in a conditional compilation statement.
  @Archivable
  public indirect enum Condition: Equatable, Sendable {

    /// Always holds.
    case `true`

    /// Never holds.
    case `false`

    /// Holds iff the operating system for which the code is compiled matches the payload.
    case operatingSystem(Parsed<String>)

    /// Holds iff the processor architecture for which the code is compiled matches the payload.
    case architecture(Parsed<String>)

    /// Holds iff the payload matches any of the feature enabled in the compiler.
    case feature(Parsed<String>)

    /// Holds iff the name of the compiler processing the file matches the payload.
    case compiler(Parsed<String>)

    /// Holds iff the version of the compiler processing the file, satisfies the `comparison`.
    case compilerVersion(comparison: VersionComparison)

    /// Holds iff the version of Hylo for which this file is compiled, satisfies `comparison`.
    case hyloVersion(comparison: VersionComparison)

    /// Holds iff the payload doesn't.
    case not(Condition)

    /// Holds iff both conditions in the payload do.
    case and(Condition, Condition)

    /// Holds iff either condition in the payload does.
    case or(Condition, Condition)

    /// `true` iff the body of the conditional-compilation shouldn't be parsed.
    public var mayNotNeedParsing: Bool {
      switch self {
      case .compiler:
        return true
      case .compilerVersion:
        return true
      case .hyloVersion:
        return true
      case .not(let c):
        return c.mayNotNeedParsing
      case .and(let l, let r):
        return l.mayNotNeedParsing && r.mayNotNeedParsing
      case .or(let l, let r):
        return l.mayNotNeedParsing || r.mayNotNeedParsing
      default:
        return false
      }
    }

    /// Returns `true` iff `self` holds for the current process.
    public func holds(for factors: ConditionalCompilationFactors) -> Bool {
      switch self {
      case .`true`:
        return true
      case .`false`:
        return false
      case .operatingSystem(let id):
        return id.value == factors.operatingSystem.description
      case .architecture(let id):
        return id.value == factors.architecture.description
      case .feature(let id):
        return id.value == "freestanding" && factors.freestanding
      case .compiler(let id):
        return id.value == "hc"
      case .compilerVersion(let comparison):
        return comparison.evaluate(for: factors.compilerVersion)
      case .hyloVersion(let comparison):
        return comparison.evaluate(for: factors.hyloVersion)
      case .not(let c):
        return !c.holds(for: factors)
      case .and(let l, let r):
        return l.holds(for: factors) && r.holds(for: factors)
      case .or(let l, let r):
        return l.holds(for: factors) || r.holds(for: factors)
      }
    }

  }

  /// The introducer of this expression.
  public let introducer: Token

  /// The condition.
  public let condition: Condition

  /// The statements in the block.
  public let statements: [StatementIdentity]

  /// The statements to be used if the condition is false.
  public let fallback: [StatementIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Token,
    condition: Condition,
    statements: [StatementIdentity],
    fallback: [StatementIdentity],
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.site = site
    self.condition = condition
    self.statements = statements
    self.fallback = fallback
  }

  /// Returns the statements that this expands to.
  public func expansion(for factors: ConditionalCompilationFactors) -> [StatementIdentity] {
    condition.holds(for: factors) ? statements : fallback
  }

}

extension ConditionalCompilation.VersionComparison: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .greaterOrEqual(let v):
      return ">= \(printer.show(v))"
    case .less(let v):
      return "< \(printer.show(v))"
    }
  }

}

extension ConditionalCompilation.Condition: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .`true`:
      return "true"
    case .`false`:
      return "false"
    case .operatingSystem(let id):
      return "os(\(id))"
    case .architecture(let id):
      return "arch(\(id))"
    case .feature(let id):
      return "feature(\(id))"
    case .compiler(let id):
      return "compiler(\(id))"
    case .compilerVersion(let comparison):
      return "compilerVersion(\(printer.show(comparison)))"
    case .hyloVersion(let comparison):
      return "hyloVersion(\(printer.show(comparison)))"
    case .not(let c):
      return "!(\(printer.show(c)))"
    case .and(let l, let r):
      return "(\(printer.show(l)) && \(printer.show(r)))"
    case .or(let l, let r):
      return "(\(printer.show(l)) || \(printer.show(r)))"
    }
  }

}

extension ConditionalCompilation: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "#if \(printer.show(condition)) {\n"
    for s in statements { result.append(printer.show(s).indented + "\n") }
    if !fallback.isEmpty {
      result.append("} else {\n")
      for s in fallback { result.append(printer.show(s).indented + "\n") }
    }
    result.append("}")
    return result
  }

}

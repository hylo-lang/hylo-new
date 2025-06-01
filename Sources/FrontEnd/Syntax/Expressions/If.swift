import Archivist

/// A conditional expression with two branches.
@Archivable
public struct If: Expression, Scope {

  /// The identity of the else-branch of an if-expression.
  public struct ElseIdentity: SyntaxIdentity {

    /// The type-erased value of this identity.
    public let erased: AnySyntaxIdentity

    /// Creates an identifying the same node as `erased`.
    public init(uncheckedFrom erased: AnySyntaxIdentity) {
      self.erased = erased
    }

    /// Creates an instance equal to `other`.
    public init(_ other: If.ID) {
      self.erased = other.erased
    }

    /// Creates an instance equal to `other`.
    public init(_ other: Block.ID) {
      self.erased = other.erased
    }

  }

  /// The introducer of this expression.
  public let introducer: Token

  /// The list of conditions of this expression, which is not empty.
  public let conditions: [ConditionIdentity]

  /// The code executed if the condition holds.
  public let success: Block.ID

  /// The code executed if the condition does not hold, if any.
  public let failure: ElseIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    introducer: Token,
    conditions: [ConditionIdentity],
    success: Block.ID,
    failure: ElseIdentity,
    site: SourceSpan
  ) {
    self.introducer = introducer
    self.conditions = conditions
    self.success = success
    self.failure = failure
    self.site = site
  }

}

extension If: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "if \(printer.show(conditions)) "
    result.append(printer.show(success))
    result.append(" else ")
    result.append(printer.show(failure))
    return result
  }

}

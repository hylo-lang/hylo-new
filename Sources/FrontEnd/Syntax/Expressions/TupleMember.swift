import Archivist

/// A reference to a member of a tuple.
@Archivable
public struct TupleMember: Expression {

  /// The expression of the tuple that contains the selected member.
  public let parent: ExpressionIdentity

  /// The 0-based index of the selected member.
  public let member: Parsed<Int>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(parent: ExpressionIdentity, member: Parsed<Int>, site: SourceSpan) {
    self.parent = parent
    self.member = member
    self.site = site
  }

}

extension TupleMember: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(parent)).\(member.value)"
  }

}

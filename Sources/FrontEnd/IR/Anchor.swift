/// A region of the source code to which IR can be associated.
public struct Anchor: Hashable, Sendable {

  /// The site of `self`.
  public let site: SourceSpan

  /// The lexical scope that notionally contains this anchor.
  ///
  /// This information is used during IR analysis to determine the implicit context in which the
  /// expression from which the IR was lowered.
  public let scope: ScopeIdentity

}

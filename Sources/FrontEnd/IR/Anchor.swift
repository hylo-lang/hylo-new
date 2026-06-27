import Archivist

/// A region of the source code to which IR can be associated.
@Archivable
public struct Anchor: Hashable, Sendable {

  /// The site of `self`.
  public let site: SourceSpan

  /// The lexical scope that notionally contains this anchor.
  ///
  /// This information is used during IR analysis to determine the implicit context in which the
  /// expression from which the IR was lowered.
  public let scope: ScopeIdentity

  /// Creates an instance with the given properties.
  public init(site: SourceSpan, scope: ScopeIdentity) {
    self.site = site
    self.scope = scope
  }

}

extension Program {

  /// Creates an anchor attached to `d`'s introducer.
  public func anchor(introducerOf d: BindingDeclaration.ID) -> Anchor {
    .init(site: self[self[d].pattern].introducer.site, scope: parent(containing: d))
  }

  /// Creates an anchor attached to `d`'s introducer.
  public func anchor(introducerOf d: ConformanceDeclaration.ID) -> Anchor {
    .init(site: self[d].introducer.site, scope: .init(node: d))
  }

  /// Creates an anchor attached to `d`'s introducer.
  public func anchor(introducerOf d: FunctionDeclaration.ID) -> Anchor {
    .init(site: self[d].introducer.site, scope: .init(node: d))
  }

  /// Creates an anchor attached to `d`'s introducer.
  public func anchor(introducerOf d: VariantDeclaration.ID) -> Anchor {
    .init(site: self[d].effect.site, scope: .init(node: d))
  }

}

import Archivist
import Utilities

/// A region of the source code to which IR can be associated.
@Archivable
public struct Anchor: Hashable, Sendable {

  /// The position at the start of the region covered by `self`.
  public let start: LineAndUTF16Offset

  /// The position immediately after the end of the region covered by `self`.
  public let end: LineAndUTF16Offset

  /// The lexical scope that notionally contains this anchor.
  ///
  /// This information is used during IR analysis to determine the implicit context in which the
  /// expression from which the IR was lowered.
  public let scope: ScopeIdentity

  fileprivate init(start: LineAndUTF16Offset, end: LineAndUTF16Offset, scope: ScopeIdentity) {
    self.start = start
    self.end = end
    self.scope = scope
  }

  /// Creates an instance with the given properties.
  fileprivate init(site: SourceSpan, scope: ScopeIdentity) {
    self.start = site.start.lineAndUTF16Offset
    self.end = site.end.lineAndUTF16Offset
    self.scope = scope
  }

  /// Returns an anchor attached to the end of the region to which `self` is attached.
  public var emptyAtEnd: Anchor {
    .init(start: end, end: end, scope: scope)
  }

}

extension Program {

  /// Creates an anchor attached to `site`, which is the same file as `scope`.
  public func anchor(at site: SourceSpan, in scope: ScopeIdentity) -> Anchor {
    assert(modules.values[scope.module][scope.file].source == site.source)
    return .init(site: site, scope: scope)
  }

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

  /// Returns an anchor suitable to generate debug information related to `n` as a whole.s
  public func anchorForDiagnostics<T: SyntaxIdentity>(about n: T) -> Anchor {
    .init(site: spanForDiagnostic(about: n), scope: parent(containing: n))
  }

  /// Returns the region of text to which `anchor` is attached.
  public func span(_ anchor: Anchor) -> SourceSpan {
    let source = modules.values[anchor.scope.module][anchor.scope.file].source
    let x0 = source.index(line: anchor.start.line, utf16Offset: anchor.start.offset)
    let x1 = source.index(line: anchor.end.line, utf16Offset: anchor.end.offset)
    return .init(x0 ..< x1, in: source)
  }

}

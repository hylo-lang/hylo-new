import SwiftSyntax

/// A rewriter that pads the multiline bodies of type, extension, and protocol declarations with a
/// blank line after the opening brace and before the closing brace.
///
/// Bodies that are empty or written on a single line are left unchanged.
public final class TypeBodyBlankLines: SyntaxRewriter {

  /// Creates an instance.
  public override init(viewMode: SyntaxTreeViewMode = .sourceAccurate) {
    super.init(viewMode: viewMode)
  }

  public override func visit(_ node: MemberBlockSyntax) -> MemberBlockSyntax {
    var transformed = super.visit(node)
    guard var first = transformed.members.first else { return transformed }

    if let t = first.leadingTrivia.paddedWithBlankLineAtFirstBreak() {
      first.leadingTrivia = t
      transformed.members[transformed.members.startIndex] = first
    }
    if let t = transformed.rightBrace.leadingTrivia.paddedWithBlankLineAtLastBreak() {
      transformed.rightBrace.leadingTrivia = t
    }
    return transformed
  }

}

extension Trivia {

  /// Returns `self` with its first line break widened to span a blank line, `nil` if `self`
  /// contains no line break or already contains a blank line at its first break.
  fileprivate func paddedWithBlankLineAtFirstBreak() -> Trivia? {
    pieces.firstIndex(where: \.isNewline).flatMap(paddedWithBlankLine(at:))
  }

  /// Returns `self` with its last line break widened to span a blank line, `nil` if `self`
  /// contains no line break or already contains a blank line at its last break.
  fileprivate func paddedWithBlankLineAtLastBreak() -> Trivia? {
    pieces.lastIndex(where: \.isNewline).flatMap(paddedWithBlankLine(at:))
  }

  /// Returns `self` with the line break at `i` widened to span a blank line, or `nil` if it
  /// already does.
  ///
  /// - Requires: The piece at `i` is a line break.
  private func paddedWithBlankLine(at i: Int) -> Trivia? {
    var ps = pieces
    switch ps[i] {
    case .newlines(1):
      ps[i] = .newlines(2)
    case .carriageReturnLineFeeds(1):
      ps[i] = .carriageReturnLineFeeds(2)
    case .carriageReturns(1):
      ps[i] = .carriageReturns(2)
    default:
      return nil
    }
    return Trivia(pieces: ps)
  }

}

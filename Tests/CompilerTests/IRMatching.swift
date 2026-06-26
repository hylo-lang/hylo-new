import Utilities

/// Matching of an observed compiler artifact against an expected one.
///
/// This type contains XCTest-independent logic used by the compiler tests to decide what
/// must be compared. It supports any line-oriented, section-structured artifact.
enum IRMatching {

  /// An equality that must hold for an observed artifact to satisfy an expectation.
  struct Comparison: Equatable {

    /// A fragment of the expected artifact.
    let expected: Substring

    /// The fragment of the observed artifact that should equal `expected`, or `nil` if there were
    /// no fragments observed.
    let observed: Substring?

  }

  /// Returns the comparisons to perform to check that `observed` satisfies `expected`.
  ///
  /// Each *section* of `expected` is matched independently against a section of `observed`, so the
  /// result has one comparison per expected section. Sections of `observed` with no counterpart in
  /// `expected` are ignored, making `expected` a partial specification of `observed`.
  ///
  /// A section is a maximal run of consecutive non-blank lines. An expected section is matched
  /// against the observed section having the most similar first line.
  static func comparisons(expected: String, observed: String) -> [Comparison] {
    let observed = Array(sections(of: observed.normalizedLineEndings()))

    // Index the observed sections by their first line so the common case (an exact match) is just a lookup.
    var byFirstLine: [Substring: Substring] = [:]
    for s in observed {
      byFirstLine[s.firstLine] = byFirstLine[s.firstLine] ?? s
    }

    return sections(of: expected.normalizedLineEndings()).map { (e) in
      let head = e.firstLine

      // Happy path: an observed section with the same first line. Otherwise, fall back to the one
      // whose first line is the most similar.
      let matched =
        byFirstLine[head] ?? observed.min(measuredBy: { (s) in distance(head, s.firstLine) })

      return Comparison(expected: e, observed: matched)
    }
  }

  /// Returns an iterator over the sections of `s`, in order of appearance.
  ///
  /// A section is a maximal run of consecutive non-blank lines, where a line is blank if it's empty
  /// or contains only whitespace. Sections are yielded as slices of `s` in a single forward pass.
  static func sections(of s: String) -> AnyIterator<Substring> {
    var i = s.startIndex
    var done = false

    // Returns the next line of `s`—excluding its terminating newline—or `nil` once every line has
    // been consumed. As in `split(omittingEmptySubsequences: false)`, a trailing newline yields a
    // final empty line.
    func nextLine() -> Substring? {
      if done { return nil }
      let start = i
      while (i != s.endIndex) && !s[i].isNewline { i = s.index(after: i) }
      let line = s[start ..< i]
      if i == s.endIndex { done = true } else { i = s.index(after: i) }
      return line
    }

    return AnyIterator { () -> Substring? in
      // Skip blank lines until the start of the next section, if any.
      var line = nextLine()
      while let l = line, l.allSatisfy(\.isWhitespace) { line = nextLine() }
      guard let head = line else { return nil }

      // Extend the section across consecutive non-blank lines.
      var end = head.endIndex
      while let l = nextLine() {
        if l.allSatisfy(\.isWhitespace) { break }
        end = l.endIndex
      }
      return s[head.startIndex ..< end]
    }
  }

}

/// Returns the smallest number of additions and deletions that transform `b` into `a`.
private func distance(_ a: Substring, _ b: Substring) -> Int {
  a.difference(from: b).count
}

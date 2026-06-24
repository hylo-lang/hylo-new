import Utilities

/// Matching of an observed compiler artifact against an expected one.
///
/// This type contains XCTest-independent logic used by the compiler tests to decide what
/// must be compared. It supports any line-oriented, section-structured artifact.
enum IRMatching {

  /// An equality that must hold for an observed artifact to satisfy an expectation.
  struct Comparison: Equatable {

    /// A fragment of the expected artifact.
    let expected: String

    /// The fragment of the observed artifact that should equal `expected`, or `nil` if there were
    /// no fragments observed.
    let observed: String?

  }

  /// A list of consecutive non-blank lines.
  typealias Section = [Substring]

  /// Returns the comparisons to perform to check that `observed` satisfies `expected`.
  ///
  /// Each *section* of `expected` is matched independently against a section of `observed`, so the
  /// result has one comparison per expected section. Sections of `observed` with no counterpart in
  /// `expected` are ignored, making `expected` a partial specification of `observed`.
  ///
  /// A section is a maximal run of consecutive non-blank lines. An expected section is matched
  /// against the observed section having the most similar first line.
  static func comparisons(expected: String, observed: String) -> [Comparison] {
    let expected = sections(of: expected.normalizedLineEndings())
    let observed = sections(of: observed.normalizedLineEndings())

    return expected.map { (e) in
      let head = e[0]

      // Pair with the observed section having the most similar first line.
      let matched = observed.min(by: { (s) in distance(head, s[0]) })

      return Comparison(
        expected: e.joined(separator: "\n"),
        observed: matched.map({ (m) in m.joined(separator: "\n") }))
    }
  }

  /// Returns the sections of `s`, in order of appearance.
  ///
  /// A section is a maximal run of consecutive non-blank lines, where a line is blank if it's empty
  /// or contains only whitespace.
  static func sections(of s: String) -> [Section] {
    s.split(separator: "\n", omittingEmptySubsequences: false)
      .split(whereSeparator: { $0.allSatisfy(\.isWhitespace) })
      .map(Array.init)
  }

}

/// Returns the smallest number of additions and deletions that transform `b` into `a`.
private func distance(_ a: Substring, _ b: Substring) -> Int {
  a.difference(from: b).count
}

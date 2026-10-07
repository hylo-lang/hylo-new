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
  /// The function-local names of both sides are canonicalized before they are compared, so that
  /// the comparison is insensitive to the names given to registers, parameters, and basic blocks.
  static func comparisons(expected: String, observed: String) -> [Comparison] {
    let observed = sections(of: observed.normalizedLineEndings()).map { (s) in
      Substring(canonicalizingNames(in: s))
    }

    // Index the observed sections by their first line so the common case (an exact match) is just
    // a lookup.
    var byFirstLine: [Substring: Substring] = [:]
    for s in observed {
      byFirstLine[s.firstLine].orAssign(s)
    }

    return sections(of: expected.normalizedLineEndings()).map { (section) in
      let e = Substring(canonicalizingNames(in: section))
      let head = e.firstLine

      // Happy path: an observed section with the same first line. Otherwise, fall back to the one
      // whose first line is the most similar.
      let matched =
        byFirstLine[head] ?? observed.min(measuredBy: { (s) in distance(head, s.firstLine) })

      return Comparison(expected: e, observed: matched)
    }
  }

  /// Returns `s` with its function-local names renumbered in order of first appearance.
  ///
  /// Both Hylo IR and LLVM IR designate registers, parameters, and basic blocks by function-local
  /// names that shift whenever an unrelated instruction is inserted or removed. Renumbering these
  /// names in order of first appearance gives a canonical form in which two sections are equal iff
  /// they are identical up to a consistent renaming of those names, so that an expectation may
  /// use any names it likes (e.g., `%result` for `%6`, or `%x` for `%r2`).
  ///
  /// A name is `%` followed by alphanumeric characters and underscores (e.g., `%6`, `%r2`, `%p0`,
  /// `%b1`, `%result`), or the label `N:` of an unnamed LLVM basic block, which denotes `%N`.
  /// Quoted LLVM names (e.g., `%"$hsInt32"`) are left untouched.
  static func canonicalizingNames(in s: Substring) -> String {
    /// The canonical number of each name seen so far, keyed by its spelling without `%`.
    var renaming: [Substring: Int] = [:]
    let name = /%(?<register>[A-Za-z0-9_]+)|^(?<label>[0-9]+)(?=:)/.anchorsMatchLineEndings()

    return String(s.replacing(name) { (m) in
      let spelling = m.register ?? m.label!
      let n = renaming[spelling] ?? renaming.count
      renaming[spelling] = n
      return ((m.register == nil) ? "" : "%") + String(n)
    })
  }

  /// Returns the sections of `s`, in order of appearance.
  ///
  /// A section is a maximal run of consecutive non-blank lines, where a line is blank if it is
  /// empty or contains only whitespace. As an exception, blank lines followed by the label of an
  /// LLVM basic block (e.g., `9:`) do not end a section, so that a function's blocks stay in the
  /// same section as its header. Sections are slices of `s`.
  static func sections(of s: String) -> [Substring] {
    var result: [Substring] = []
    var previousLineIsBlank = true

    for l in s.split(omittingEmptySubsequences: false, whereSeparator: \.isNewline) {
      defer { previousLineIsBlank = l.isBlank }
      if l.isBlank { continue }

      // Extend the current section unless a blank line ended it, or start a new one.
      if let last = result.last, !previousLineIsBlank || l.isBasicBlockLabel {
        result[result.count - 1] = s[last.startIndex ..< l.endIndex]
      } else {
        result.append(l)
      }
    }

    return result
  }

}

/// Returns the smallest number of additions and deletions that transform `b` into `a`.
private func distance(_ a: Substring, _ b: Substring) -> Int {
  a.difference(from: b).count
}

extension Substring {

  /// `true` iff `self` is empty or contains only whitespace.
  fileprivate var isBlank: Bool {
    allSatisfy(\.isWhitespace)
  }

  /// `true` iff `self` is a line labeling an LLVM basic block, i.e., a line that starts with a
  /// number followed by a colon (e.g., `9:   ; preds = %4`).
  fileprivate var isBasicBlockLabel: Bool {
    prefixMatch(of: /[0-9]+:/) != nil
  }

}

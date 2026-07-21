import Testing

struct IRMatchingTests {

  // MARK: comparisons

  @Test func markerlessInputIsMatchedAsSections() {
    let cs = IRMatching.comparisons(expected: "a\nb", observed: "a\nc")
    #expect(cs == [.init(expected: "a\nb", observed: "a\nc")])
  }

  @Test func normalizesLineEndings() {
    let cs = IRMatching.comparisons(expected: "a\r\nb", observed: "a\r\nb")
    #expect(cs == [.init(expected: "a\nb", observed: "a\nb")])
  }

  @Test func partialMatchesByGlobalSymbol() {
    let expected = """
      define i32 @"foo"() {
        ret i32 0
      }
      """
    let observed = """
      define void @"bar"() {
        ret void
      }

      define i32 @"foo"() {
        ret i32 0
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 1)
    #expect(cs[0].expected == "define i32 @\"foo\"() {\n  ret i32 0\n}")
    #expect(cs[0].observed == cs[0].expected)
  }

  @Test func partialReportsMismatchInMatchedSection() {
    let expected = """
      define i32 @"foo"() {
        ret i32 0
      }
      """
    let observed = """
      define i32 @"foo"() {
        ret i32 1
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 1)
    #expect(cs[0].observed != nil)
    #expect(cs[0].expected != cs[0].observed)
  }

  @Test func partialMatchesEachSectionIndependentlyAndIgnoresOrder() {
    let expected = """
      define i32 @"a"() {
        ret i32 0
      }

      define i32 @"b"() {
        ret i32 1
      }
      """
    let observed = """
      define i32 @"b"() {
        ret i32 1
      }

      define i32 @"a"() {
        ret i32 0
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 2)
    for c in cs { #expect(c.expected == c.observed) }
  }

  @Test func partialFallsBackToClosestFirstLineWhenNoSymbol() {
    let expected = """
      %T = type { i32 }
      """
    let observed = """
      %U = type { i64 }

      %T = type { i32. }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 1)
    // The closest observed section is chosen even though it isn't identical to the expected one.
    #expect(cs[0].observed == "%T = type { i32. }")
  }

  @Test func partialUnmatchedWhenObservedHasNoSection() {
    let cs = IRMatching.comparisons(
      expected: "define void @\"f\"() {\n}", observed: "\n  \n")
    #expect(cs.count == 1)
    #expect(cs[0].observed == nil)
  }

  // MARK: comparisons (Hylo IR)

  @Test func hyloPartialMatchesByFirstLineIgnoringOrder() {
    let expected = """
      fun main(set %p0: Int32) {
        %r0 = return
      }
      """
    let observed = """
      fun use(_:)<T>(let %p0: T) {
        %r0 = return
      }

      fun main(set %p0: Int32) {
        %r0 = return
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 1)
    #expect(cs[0].expected == "fun main(set %p0: Int32) {\n  %r0 = return\n}")
    #expect(cs[0].observed == cs[0].expected)
  }

  @Test func hyloPartialReportsMismatchInMatchedSection() {
    let expected = """
      fun main(set %p0: Int32) {
        %r0 = return
      }
      """
    let observed = """
      fun main(set %p0: Int32) {
        %r0 = alloca Void
        %r1 = return
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 1)
    #expect(cs[0].observed != nil)
    #expect(cs[0].expected != cs[0].observed)
  }

  @Test func hyloPartialFallsBackToClosestFirstLine() {
    let expected = """
      fun main(set %p0: Int32) {
        %r0 = return
      }
      """
    // No exact first-line match: the body changes the signature slightly. Closest section wins.
    let observed = """
      fun helper(let %p0: Void) {
        %r0 = return
      }

      fun main(set %p0: Int64) {
        %r0 = return
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    #expect(cs.count == 1)
    #expect(cs[0].observed == "fun main(set %p0: Int64) {\n  %r0 = return\n}")
  }

  // MARK: sections

  @Test func sectionsSplitsOnBlankAndWhitespaceOnlyLines() {
    let s = "a\nb\n\nc\n   \nd\n"
    #expect(Array(IRMatching.sections(of: s)) == ["a\nb", "c", "d"])
  }

  @Test func sectionsOfEmptyInputIsEmpty() {
    #expect(Array(IRMatching.sections(of: "")).count == 0)
    #expect(Array(IRMatching.sections(of: "\n  \n")).count == 0)
  }

  @Test func sectionsSkipsLeadingBlankLines() {
    let s = "\n  \n\t\na\nb"
    #expect(Array(IRMatching.sections(of: s)) == ["a\nb"])
  }

  @Test func sectionsIgnoresTrailingBlankLines() {
    let s = "a\nb\n\n  \n"
    #expect(Array(IRMatching.sections(of: s)) == ["a\nb"])
  }

  @Test func sectionsCollapsesConsecutiveBlankLinesBetweenSections() {
    let s = "a\n\n\n\nb"
    #expect(Array(IRMatching.sections(of: s)) == ["a", "b"])
  }

  @Test func sectionsTreatsTabsAndSpacesAsBlankSeparators() {
    let s = "a\n\t \t\nb"
    #expect(Array(IRMatching.sections(of: s)) == ["a", "b"])
  }

  @Test func sectionsSingleSectionWithoutTrailingNewline() {
    let s = "only\nsection"
    #expect(Array(IRMatching.sections(of: s)) == ["only\nsection"])
  }

  @Test func sectionsPreservesLeadingAndInteriorWhitespaceWithinALine() {
    let s = "  indented\n    body  \n\nnext"
    #expect(Array(IRMatching.sections(of: s)) == ["  indented\n    body  ", "next"])
  }

  @Test func sectionsOfSingleNonBlankLine() {
    #expect(Array(IRMatching.sections(of: "a")) == ["a"])
  }

}

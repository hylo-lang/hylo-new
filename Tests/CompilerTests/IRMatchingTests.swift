import XCTest

final class IRMatchingTests: XCTestCase {

  // MARK: comparisons

  func testMarkerlessInputIsMatchedAsSections() {
    let cs = IRMatching.comparisons(expected: "a\nb", observed: "a\nc")
    XCTAssertEqual(cs, [.init(expected: "a\nb", observed: "a\nc")])
  }

  func testNormalizesLineEndings() {
    let cs = IRMatching.comparisons(expected: "a\r\nb", observed: "a\r\nb")
    XCTAssertEqual(cs, [.init(expected: "a\nb", observed: "a\nb")])
  }

  func testPartialMatchesByGlobalSymbol() {
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
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].expected, "define i32 @\"foo\"() {\n  ret i32 0\n}")
    XCTAssertEqual(cs[0].observed, cs[0].expected)
  }

  func testPartialReportsMismatchInMatchedSection() {
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
    XCTAssertEqual(cs.count, 1)
    XCTAssertNotNil(cs[0].observed)
    XCTAssertNotEqual(cs[0].expected, cs[0].observed)
  }

  func testPartialMatchesEachSectionIndependentlyAndIgnoresOrder() {
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
    XCTAssertEqual(cs.count, 2)
    for c in cs { XCTAssertEqual(c.expected, c.observed) }
  }

  func testPartialFallsBackToClosestFirstLineWhenNoSymbol() {
    let expected = """
      %T = type { i32 }
      """
    let observed = """
      %U = type { i64 }

      %T = type { i32. }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    // The closest observed section is chosen even though it isn't identical to the expected one.
    XCTAssertEqual(cs[0].observed, "%T = type { i32. }")
  }

  func testPartialUnmatchedWhenObservedHasNoSection() {
    let cs = IRMatching.comparisons(
      expected: "define void @\"f\"() {\n}", observed: "\n  \n")
    XCTAssertEqual(cs.count, 1)
    XCTAssertNil(cs[0].observed)
  }

  // MARK: comparisons (Hylo IR)

  func testHyloPartialMatchesByFirstLineIgnoringOrder() {
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
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].expected, "fun main(set %p0: Int32) {\n  %r0 = return\n}")
    XCTAssertEqual(cs[0].observed, cs[0].expected)
  }

  func testHyloPartialReportsMismatchInMatchedSection() {
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
    XCTAssertEqual(cs.count, 1)
    XCTAssertNotNil(cs[0].observed)
    XCTAssertNotEqual(cs[0].expected, cs[0].observed)
  }

  func testHyloPartialFallsBackToClosestFirstLine() {
    let expected = """
      fun main(set %p0: Int32) {
        %r0 = return
      }
      """
    // No exact first-line match: the body changes the signature slightly. The closest section wins.
    let observed = """
      fun helper(let %p0: Void) {
        %r0 = return
      }

      fun main(set %p0: Int64) {
        %r0 = return
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].observed, "fun main(set %p0: Int64) {\n  %r0 = return\n}")
  }

  // MARK: sections

  func testSectionsSplitsOnBlankAndWhitespaceOnlyLines() {
    let s = "a\nb\n\nc\n   \nd\n"
    XCTAssertEqual(IRMatching.sections(of: s), [["a", "b"], ["c"], ["d"]])
  }

  func testSectionsOfEmptyInputIsEmpty() {
    XCTAssertEqual(IRMatching.sections(of: "").count, 0)
    XCTAssertEqual(IRMatching.sections(of: "\n  \n").count, 0)
  }

}

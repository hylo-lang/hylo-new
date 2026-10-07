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
      %"T" = type <{ i32 }>
      """
    let observed = """
      %"U" = type <{ i64 }>

      %"T" = type <{ i32. }>
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    // The closest observed section is chosen even though it isn't identical to the expected one.
    XCTAssertEqual(cs[0].observed, "%\"T\" = type { i32. }")
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
    XCTAssertEqual(cs[0].expected, "fun main(set %0: Int32) {\n  %1 = return\n}")
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
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].observed, "fun main(set %0: Int64) {\n  %1 = return\n}")
  }

  // MARK: canonicalizingNames

  /// LLVM values are renumbered in order of first appearance.
  func testLLVMRenumbering() {
    let s = """
      define i32 @"f"(ptr %0, ptr %1) {
        %7 = alloca i32, align 4
        %12 = load i32, ptr %7, align 4
        ret i32 %12
      }
      """
    let expected = """
      define i32 @"f"(ptr %0, ptr %1) {
        %2 = alloca i32, align 4
        %3 = load i32, ptr %2, align 4
        ret i32 %3
      }
      """
    XCTAssertEqual(IRMatching.canonicalizingNames(in: Substring(s)), expected)
  }

  /// A block label `N:` and its references `%N` are the same name.
  func testLLVMLabels() {
    let s = """
      define void @"f"() {
        br label %9

      9:                                                ; preds = %4
        ret void
      }
      """
    let expected = """
      define void @"f"() {
        br label %0

      0:                                                ; preds = %1
        ret void
      }
      """
    XCTAssertEqual(IRMatching.canonicalizingNames(in: Substring(s)), expected)
  }

  /// Named values are renumbered like unnamed ones; quoted names are left untouched.
  func testLLVMNamedValues() {
    let s = """
      %"$hsInt32" = type { i32 }
      define %"$hsInt32" @"f"(%"$hsInt32" %x, i32 %2) {
        %result = alloca %"$hsInt32", align 4
        ret %"$hsInt32" zeroinitializer
      }
      """
    let expected = """
      %"$hsInt32" = type { i32 }
      define %"$hsInt32" @"f"(%"$hsInt32" %0, i32 %1) {
        %2 = alloca %"$hsInt32", align 4
        ret %"$hsInt32" zeroinitializer
      }
      """
    XCTAssertEqual(IRMatching.canonicalizingNames(in: Substring(s)), expected)
  }

  /// Hylo parameters, blocks, and registers share a single numbering.
  func testHyloRenumbering() {
    let s = """
      fun main(set %p1: Int32, let %p0: Void) {
      %b3:
        %r15 = alloca Void, #preferred
        %r2 = access [set] %r15
        %r7 = branch %b0
      %b0:
        %r1 = end %r2
        %r0 = return
      }
      """
    let expected = """
      fun main(set %0: Int32, let %1: Void) {
      %2:
        %3 = alloca Void, #preferred
        %4 = access [set] %3
        %5 = branch %6
      %6:
        %7 = end %4
        %8 = return
      }
      """
    XCTAssertEqual(IRMatching.canonicalizingNames(in: Substring(s)), expected)
  }

  /// A name is the whole identifier, so `%3` and `%30` are distinct.
  func testPrefixedNames() {
    XCTAssertEqual(
      IRMatching.canonicalizingNames(in: "%3 %30 %3 %r1 %r10 %r1 %r_1"),
      "%0 %1 %0 %2 %3 %2 %4")
  }

  func testIdempotence() {
    let s = "%9 = add i32 %1, %1\n%10 = add i32 %9, %2"
    let once = IRMatching.canonicalizingNames(in: Substring(s))
    XCTAssertEqual(IRMatching.canonicalizingNames(in: Substring(once)), once)
  }

  /// Sections that only differ by their numbering compare equal.
  func testRenumberedSectionsMatch() {
    let expected = """
      define i32 @"f"(ptr %0) {
        %2 = alloca i32, align 4
        %result = load i32, ptr %2, align 4
        ret i32 %result
      }
      """
    let observed = """
      define i32 @"f"(ptr %0) {
        %5 = alloca i32, align 4
        %6 = load i32, ptr %5, align 4
        ret i32 %6
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].expected, cs[0].observed)
  }

  /// Hylo IR using named registers matches ir with numbered registers.
  func testHyloNamedRegistersMatch() {
    let expected = """
      fun main(set %out: Int32) {
      %entry:
        %x = alloca Int32, #preferred
        %r = access [set] %x
        %end_r = end %r
        %ret = return
      }
      """
    let observed = """
      fun main(set %p0: Int32) {
      %b0:
        %r0 = alloca Int32, #preferred
        %r1 = access [set] %r0
        %r2 = end %r1
        %r3 = return
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].expected, cs[0].observed)
  }

  /// Sections whose data flow differs are not conflated by renumbering.
  func testDataFlowMismatch() {
    let expected = """
      define i32 @"f"(ptr %0) {
        %2 = load i32, ptr %0, align 4
        %3 = load i32, ptr %0, align 4
        ret i32 %2
      }
      """
    let observed = """
      define i32 @"f"(ptr %0) {
        %2 = load i32, ptr %0, align 4
        %3 = load i32, ptr %0, align 4
        ret i32 %3
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    XCTAssertNotEqual(cs[0].expected, cs[0].observed)
  }

  // MARK: sections

  func testSectionsSplitsOnBlankAndWhitespaceOnlyLines() {
    let s = "a\nb\n\nc\n   \nd\n"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["a\nb", "c", "d"])
  }

  /// The blank line preceding an LLVM block label does not end a section.
  func testSectionsSpanLLVMBlocks() {
    let s = """
      define void @"f"() {
        br label %2

      2:                                                ; preds = %0
        br label %3

      3:                                                ; preds = %2
        ret void
      }

      define void @"g"() {
        ret void
      }
      """
    let ss = Array(IRMatching.sections(of: s))
    XCTAssertEqual(ss.count, 2)
    XCTAssertEqual(ss[0].firstLine, "define void @\"f\"() {")
    XCTAssertTrue(ss[0].hasSuffix("; preds = %2\n  ret void\n}"))
    XCTAssertEqual(ss[1], "define void @\"g\"() {\n  ret void\n}")
  }

  func testBlocksPairedByFunction() {
    let expected = """
      define void @"g"() {
        br label %5

      5:                                                ; preds = %0
        call void @"h"()
        ret void
      }
      """
    let observed = """
      define void @"f"() {
        br label %1

      1:                                                ; preds = %0
        ret void
      }

      define void @"g"() {
        br label %1

      1:                                                ; preds = %0
        call void @"h"()
        ret void
      }
      """
    let cs = IRMatching.comparisons(expected: expected, observed: observed)
    XCTAssertEqual(cs.count, 1)
    XCTAssertEqual(cs[0].expected, cs[0].observed)
  }

  func testSectionsOfEmptyInputIsEmpty() {
    XCTAssertEqual(Array(IRMatching.sections(of: "")).count, 0)
    XCTAssertEqual(Array(IRMatching.sections(of: "\n  \n")).count, 0)
  }

  func testSectionsSkipsLeadingBlankLines() {
    let s = "\n  \n\t\na\nb"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["a\nb"])
  }

  func testSectionsIgnoresTrailingBlankLines() {
    let s = "a\nb\n\n  \n"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["a\nb"])
  }

  func testSectionsCollapsesConsecutiveBlankLinesBetweenSections() {
    let s = "a\n\n\n\nb"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["a", "b"])
  }

  func testSectionsTreatsTabsAndSpacesAsBlankSeparators() {
    let s = "a\n\t \t\nb"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["a", "b"])
  }

  func testSectionsSingleSectionWithoutTrailingNewline() {
    let s = "only\nsection"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["only\nsection"])
  }

  func testSectionsPreservesLeadingAndInteriorWhitespaceWithinALine() {
    let s = "  indented\n    body  \n\nnext"
    XCTAssertEqual(Array(IRMatching.sections(of: s)), ["  indented\n    body  ", "next"])
  }

  func testSectionsOfSingleNonBlankLine() {
    XCTAssertEqual(Array(IRMatching.sections(of: "a")), ["a"])
  }

}

import FrontEnd
import XCTest

/// A collection of tests for `assemblySanitized` extensions to `String`.
final class AssemblySanitizedTests: XCTestCase {

  /// Tests that `isAssemblySuitable` correctly identifies strings that are suitable for assembly
  /// symbols, for a few examples.
  func testIsAssemblySuitable() {
    XCTAssert("".isAssemblySuitable)
    XCTAssert("_foo".isAssemblySuitable)

    XCTAssertFalse("étoile".isAssemblySuitable)
    XCTAssertFalse("Bang!".isAssemblySuitable)
    XCTAssertFalse("谷".isAssemblySuitable)
  }

  /// Tests that the assembly sanitization of empty string is also the empty string.
  func testEmpty() {
    let s = "".assemblySanitized
    XCTAssertEqual(s, "")
    XCTAssertEqual(String(assemblySanitized: s), "")
  }

  /// Tests that strings that do not require sanitization remain unchanged.
  func testNoSanitization() {
    XCTAssertEqual("abc123".assemblySanitized, "abc123")
    XCTAssertEqual("_foo".assemblySanitized, "_foo")
  }

  /// A few examples of names to test with.
  private let examples = [
    "infix+++",
    "日本語",
    "Bang!",
    "étoile",
    "ALL men by nature desire to know",
    ".",
    "$",
    "!@#$%^&*()_+",
    "foo$bar",
  ]

  /// Tests that strings containing symbols are sanitized correctly.
  func testSanitization() {
    for example in examples {
      let s = example.assemblySanitized
      XCTAssert(s.isAssemblySuitable)
    }
  }

  /// Tests that the desanitization is a reverse operation of sanitization, for a few examples.
  func testDesanitization() {
    for example in examples {
      XCTAssertEqual(String(assemblySanitized: example.assemblySanitized), example)
    }
  }

}

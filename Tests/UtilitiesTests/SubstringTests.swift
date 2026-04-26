import Utilities
import XCTest

final class SubstringTests: XCTestCase {

  func testRemoveIfPredicate() {
    let s = "abc"
    var t = s[...]
    XCTAssert(t.removeFirst(if: { (h) in h == "a" }))
    XCTAssertEqual(t, "bc")
    XCTAssertFalse(t.removeFirst(if: { (h) in h == "a" }))
    XCTAssertEqual(t, "bc")
  }

  func testRemoveIfMatches() {
    let s = "abc"
    var t = s[...]
    XCTAssert(t.removeFirst(if: "a"))
    XCTAssertEqual(t, "bc")
    XCTAssertFalse(t.removeFirst(if: "a"))
    XCTAssertEqual(t, "bc")
  }

  func testSans() {
    let s = "vadalma"
    let t = s.sans("a")
    XCTAssertEqual(t, "vdlm")
  }

}

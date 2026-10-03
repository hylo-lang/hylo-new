import Utilities
import XCTest

final class StrictOrderingTests: XCTestCase {

  func testInitFromComparable() {
    XCTAssertEqual(StrictOrdering(between: 3, and: 5), .ascending)
    XCTAssertEqual(StrictOrdering(between: 3, and: 3), .equal)
    XCTAssertEqual(StrictOrdering(between: 5, and: 3), .descending)
  }

  func testInequalOrElse() {
    for o in StrictOrdering.allCases {
      XCTAssertEqual(StrictOrdering.ascending.inequalElse(o), .ascending)
      XCTAssertEqual(StrictOrdering.equal.inequalElse(o), o)
      XCTAssertEqual(StrictOrdering.descending.inequalElse(o), .descending)
    }
  }

  func testComparing() {
    let f = StrictOrdering.comparing(\Int.magnitude)
    XCTAssertEqual(f(3, -5), .ascending)
    XCTAssertEqual(f(3, -3), .equal)
    XCTAssertEqual(f(-5, 3), .descending)
  }

}

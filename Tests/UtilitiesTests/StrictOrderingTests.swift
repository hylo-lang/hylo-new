import Utilities
import XCTest

final class StrictOrderingTests: XCTestCase {

  func testInitFromComparable() {
    XCTAssertEqual(StrictOrdering(from: 3, to: 5), .ascending)
    XCTAssertEqual(StrictOrdering(from: 3, to: 3), .equal)
    XCTAssertEqual(StrictOrdering(from: 5, to: 3), .descending)
  }

  func testComparing() {
    let f = StrictOrdering.descriptor(ofChangeIn: \Int.magnitude)
    XCTAssertEqual(f(3, -5), .ascending)
    XCTAssertEqual(f(3, -3), .equal)
    XCTAssertEqual(f(-5, 3), .descending)
  }

}

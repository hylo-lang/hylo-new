import Utilities
import XCTest

final class StrictOrderingTests: XCTestCase {

  func testInitFromComparable() {
    XCTAssertEqual(3 <=> 5, .ascending)
    XCTAssertEqual(3 <=> 3, .equal)
    XCTAssertEqual(5 <=> 3, .descending)
  }

  func testComparing() {
    let f = threeWayComparison(of: \Int.magnitude)
    XCTAssertEqual(f(3, -5), .ascending)
    XCTAssertEqual(f(3, -3), .equal)
    XCTAssertEqual(f(-5, 3), .descending)
  }

}

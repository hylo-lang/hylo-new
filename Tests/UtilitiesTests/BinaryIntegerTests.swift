import Utilities
import XCTest

final class BinaryIntegerTests: XCTestCase {

  func testRoundedUpToNearestMultipleOf() {
    XCTAssertEqual(0.rounded(upToNearestMultipleOf: 16), 0)
    XCTAssertEqual(1.rounded(upToNearestMultipleOf: 16), 16)
    for i in (17 as UInt32) ..< 32 {
      XCTAssertEqual(i.rounded(upToNearestMultipleOf: 16), 32)
    }
  }

}

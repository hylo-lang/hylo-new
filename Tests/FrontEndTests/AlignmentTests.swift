import FrontEnd
import XCTest

final class AlignmentTests: XCTestCase {

  func testBytes() {
    XCTAssertEqual((1 as Alignment).bytes, 1)
    XCTAssertEqual(8 as Alignment, Alignment(log2: 3))
    for i in 0 ..< UInt8(Int.bitWidth - 1) {
      let a = Alignment(log2: i)
      XCTAssertEqual(a.bytes, 1 << Int(i))
      XCTAssertEqual(Alignment(bytes: a.bytes), a)
    }
  }

  func testComparison() {
    XCTAssertLessThan(Alignment(bytes: 4), Alignment(bytes: 8))
    XCTAssertEqual(max(Alignment(bytes: 2), Alignment(bytes: 16), 1), Alignment(bytes: 16))
  }

  func testRoundedUpToNearestMultipleOf() {
    let a = Alignment(bytes: 16)
    XCTAssertEqual(0.roundedUp(toNearestMultipleOf: a), 0)
    XCTAssertEqual(1.roundedUp(toNearestMultipleOf: a), 16)
    for i in (17 as UInt32) ..< 32 {
      XCTAssertEqual(i.roundedUp(toNearestMultipleOf: a), 32)
    }
    XCTAssertEqual(7.roundedUp(toNearestMultipleOf: 1), 7)
  }

  func testIsMultipleOf() {
    XCTAssert(0.isMultiple(of: Alignment(bytes: 8)))
    XCTAssert(24.isMultiple(of: Alignment(bytes: 8)))
    XCTAssertFalse(12.isMultiple(of: Alignment(bytes: 8)))
    XCTAssert(13.isMultiple(of: 1 as Alignment))
  }

}

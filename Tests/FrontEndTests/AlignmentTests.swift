import FrontEnd
import XCTest

final class AlignmentTests: XCTestCase {

  func testBytes() {
    XCTAssertEqual(Alignment(bytes: 1).bytes, 1)
    XCTAssertEqual(Alignment(bytes: 8), Alignment(log2: 3))
    for i in 0 ..< UInt8(Int.bitWidth - 1) {
      let a = Alignment(log2: i)
      XCTAssertEqual(a.bytes, 1 << Int(i))
      XCTAssertEqual(Alignment(bytes: a.bytes), a)
    }
  }

  func testComparison() {
    XCTAssertLessThan(Alignment(bytes: 4), Alignment(bytes: 8))
    XCTAssertEqual(
      max(
        Alignment(bytes: 2),
        Alignment(bytes: 16),
        Alignment(bytes: 1)),
      Alignment(bytes: 16))
  }

  func testRoundedUpToNearestMultipleOf() {
    let a = Alignment(bytes: 16)
    XCTAssertEqual(0.roundedUp(toNearestMultipleOf: a), 0)
    XCTAssertEqual(1.roundedUp(toNearestMultipleOf: a), 16)
    for i in (17 as UInt32) ..< 32 {
      XCTAssertEqual(i.roundedUp(toNearestMultipleOf: a), 32)
    }
    XCTAssertEqual(7.roundedUp(toNearestMultipleOf: .init(bytes: 1)), 7)
  }

  func testNegativeRoundedUpToNearestMultipleOf() {
    let a = Alignment(bytes: 16)
    for i in (-47 as Int32) ... -32 {
      XCTAssertEqual(i.roundedUp(toNearestMultipleOf: a), -32)
    }
    for i in (-31 as Int32) ... -16 {
      XCTAssertEqual(i.roundedUp(toNearestMultipleOf: a), -16)
    }
    for i in (-15 as Int32) ... 0 {
      XCTAssertEqual(i.roundedUp(toNearestMultipleOf: a), 0)
    }
  }

  func testIsMultipleOf() {
    for n in -33 ... 33 {
      for power in 0 ... 5 {
        let a = 1 << power
        XCTAssert((n * a).isMultiple(of: Alignment(bytes: a)))
      }
    }
  }

  func testIsMultipleOfFalse() {
    for n in -33 ... 33 {
      for power in 1 ... 5 {
        let a = 1 << power
        XCTAssertFalse((n * a - 1).isMultiple(of: Alignment(bytes: a)))
        XCTAssertFalse((n * a + 1).isMultiple(of: Alignment(bytes: a)))
      }
    }
  }

  func testNegativeIsMultipleOf() {
    XCTAssert(0.isMultiple(of: Alignment(bytes: 8)))
    XCTAssert((-24).isMultiple(of: Alignment(bytes: 8)))
    XCTAssertFalse((-12).isMultiple(of: Alignment(bytes: 8)))
    XCTAssert((-13).isMultiple(of: .init(bytes: 1)))
  }

  func testDescription() {
    XCTAssertEqual("\(Alignment.bytes(64))", "64")
  }

}

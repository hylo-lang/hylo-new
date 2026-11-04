import Utilities
import XCTest

final class BinaryIntegerTests: XCTestCase {

  func testDigits() {
    XCTAssertEqual(0.digits(width: 0), "0")
    XCTAssertEqual(7.digits(width: 2), "07")
    XCTAssertEqual(42.digits(width: 2), "42")
    XCTAssertEqual(123.digits(width: 2), "123")
  }

  func testDigitsWithRadix() {
    XCTAssertEqual(255.digits(radix: 16, width: 4), "00ff")
    XCTAssertEqual(UInt64.max.digits(radix: 16, width: 16), "ffffffffffffffff")
    XCTAssertEqual(UInt64(1).digits(radix: 16, width: 16), "0000000000000001")
    XCTAssertEqual(5.digits(radix: 2, width: 4), "0101")
  }

  func testDigitsOfNegative() {
    XCTAssertEqual((-7).digits(width: 3), "-07")
    XCTAssertEqual((-123).digits(width: 2), "-123")
    XCTAssertEqual(Int8.min.digits(width: 5), "-0128")
  }

}

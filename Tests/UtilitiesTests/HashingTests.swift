import Utilities
import XCTest

final class HashingTests: XCTestCase {

  func testCombineInt() {
    var h1 = FNV1.native()
    h1.combine(42)
    h1.combine(1337)

    var h2 = FNV1.native()
    h2.combine(42)
    h2.combine(1337)
    XCTAssertEqual(h1.state, h2.state)

    h2.combine(23)
    XCTAssertNotEqual(h1.state, h2.state)
  }

  func testCombineString() {
    var h1 = FNV1.native()
    h1.combine("a")
    h1.combine("bcd")

    var h2 = FNV1.native()
    h2.combine("a")
    h2.combine("bcd")
    XCTAssertEqual(h1.state, h2.state)

    h2.combine("xy")
    XCTAssertNotEqual(h1.state, h2.state)
  }

  func testU128() {
    var h1 = FNV1.u128()
    h1.combine(bytes: 0 ..< 10)

    var h2 = FNV1.u128()
    h2.combine(bytes: 0 ..< 10)
    XCTAssertEqual(h1.state, h2.state)

    h1.combine(11)
    XCTAssertNotEqual(h1.state, h2.state)
  }

}

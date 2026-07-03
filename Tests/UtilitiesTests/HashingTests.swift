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

  func testHashValue() {
    let s1 = FNV1.hash(0 ..< 128, into: FNV1.native())
    let s2 = FNV1.hash(0 ..< 128, into: FNV1.native())
    XCTAssertEqual(s1.state, s2.state)

    let s3 = FNV1.hash(1 ..< 129, into: FNV1.native())
    XCTAssertNotEqual(s1.state, s3.state)
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

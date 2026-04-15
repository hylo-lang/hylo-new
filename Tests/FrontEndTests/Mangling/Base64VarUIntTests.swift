import FrontEnd
import XCTest

/// A collection of tests for `Base64VarUInt`.
final class Base64VarUIntTests: XCTestCase {

  /// Tests that checks the `Base64VarUInt` encoding for a selected set of values.
  func testEncoding() {
    XCTAssertEqual(Base64VarUInt(0).description, "0")
    XCTAssertEqual(Base64VarUInt(9).description, "9")
    XCTAssertEqual(Base64VarUInt(10).description, "a")
    XCTAssertEqual(Base64VarUInt(36).description, "A")
    XCTAssertEqual(Base64VarUInt(50).description, "O")
    XCTAssertEqual(Base64VarUInt(51).description, "P0")
    XCTAssertEqual(Base64VarUInt(61).description, "Pa")
    XCTAssertEqual(Base64VarUInt(86).description, "Pz")
    XCTAssertEqual(Base64VarUInt(112).description, "PZ")
    XCTAssertEqual(Base64VarUInt(113).description, "P.")
    XCTAssertEqual(Base64VarUInt(114).description, "P_")
    XCTAssertEqual(Base64VarUInt(115).description, "Q01")
    XCTAssertEqual(Base64VarUInt(4210).description, "R1")
    XCTAssertEqual(Base64VarUInt(4211).description, "R2")
  }

  /// Test that decoding an encoded `Base64VarUInt` yields the original value.
  func testRoundTrip() {
    for i: UInt64 in 0 ..< 5000 {
      let s = Base64VarUInt(i).description
      XCTAssertEqual(Base64VarUInt(s)?.rawValue, i)
    }

    for i: UInt64 in 10000 ..< 15000 {
      let s = Base64VarUInt(i).description
      XCTAssertEqual(Base64VarUInt(s)?.rawValue, i)
    }

    for i: UInt64 in 100000 ..< 105000 {
      let s = Base64VarUInt(i).description
      XCTAssertEqual(Base64VarUInt(s)?.rawValue, i)
    }

    let specialValues: [UInt64] = [
      0x7fff_ffff, 0x8000_0000, 0xffff_ffff,
      0x7fff_ffff_ffff_ffff, 0x8000_0000_0000_0000, 0xffff_ffff_ffff_ffff,
    ]

    for i in specialValues {
      let s = Base64VarUInt(i).description
      XCTAssertEqual(Base64VarUInt(s)?.rawValue, i)
    }
  }

}

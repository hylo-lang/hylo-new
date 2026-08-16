import FrontEnd
import XCTest

@testable import Interpreter

final class RuntimeValueTests: XCTestCase {

  func testTwosComplementRepresentation() {
    XCTAssertEqual(twosComplementRepresentation(0, size: 1), 0)
    XCTAssertEqual(twosComplementRepresentation(1, size: 1), 1)
    XCTAssertEqual(twosComplementRepresentation(2, size: 1), 2)
    XCTAssertEqual(twosComplementRepresentation(-1, size: 1), 255)
    XCTAssertEqual(twosComplementRepresentation(-2, size: 1), 254)
  }

  func testRuntimeValueIntegerInitializer() {
    XCTAssertEqual(RuntimeValue(integer: 0, size: 1, alignment: 1).bytes, [0])
    XCTAssertEqual(RuntimeValue(integer: 1, size: 1, alignment: 1).bytes, [1])
    XCTAssertEqual(RuntimeValue(integer: -1, size: 1, alignment: 1).bytes, [255])
    XCTAssertEqual(RuntimeValue(integer: -2, size: 1, alignment: 1).bytes, [254])

    XCTAssertEqual(
      RuntimeValue(integer: 1, size: 2, alignment: 2).bytes,
      withUnsafeBytes(of: UInt16(1), Array.init)[...])
    XCTAssertEqual(
      RuntimeValue(integer: -1, size: 2, alignment: 2).bytes,
      withUnsafeBytes(of: UInt16(65535), Array.init)[...])

    XCTAssertEqual(
      RuntimeValue(integer: 1, size: 4, alignment: 4).bytes,
      withUnsafeBytes(of: UInt32(1), Array.init)[...])
    XCTAssertEqual(
      RuntimeValue(integer: 1, size: 8, alignment: 8).bytes,
      withUnsafeBytes(of: UInt64(1), Array.init)[...])
  }

  func testRuntimeValueAlignment() {
    for i in 1...10 {
      let b = Array(repeating: UInt8(0), count: i)
      let a = UInt(
        bitPattern: RuntimeValue(bytes: b, havingAlignment: i).bytes.withUnsafeBytes(\.baseAddress)!
      )
      XCTAssert(a % UInt(i) == 0)
    }
  }

}

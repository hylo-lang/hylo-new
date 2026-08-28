import FrontEnd
import XCTest

@testable import Interpreter

final class RuntimeValueTests: XCTestCase {

  func testTwosComplementRepresentation() {
    XCTAssertEqual(twosComplementRepresentation(0), 0)
    XCTAssertEqual(twosComplementRepresentation(1), 1)
    XCTAssertEqual(twosComplementRepresentation(2), 2)
    XCTAssertEqual(twosComplementRepresentation(-1), UInt128.max)
    XCTAssertEqual(twosComplementRepresentation(-2), UInt128.max - 1)
  }

  func testRuntimeValueIntegerInitializer() {
    XCTAssertEqual(RuntimeValue(integer: 0, bitWidth: 8, alignment: 1).bytes, [0])
    XCTAssertEqual(RuntimeValue(integer: 1, bitWidth: 8, alignment: 1).bytes, [1])
    XCTAssertEqual(RuntimeValue(integer: -1, bitWidth: 8, alignment: 1).bytes, [255])
    XCTAssertEqual(RuntimeValue(integer: -2, bitWidth: 8, alignment: 1).bytes, [254])

    XCTAssertEqual(
      RuntimeValue(integer: 1, bitWidth: 16, alignment: 2).bytes,
      withUnsafeBytes(of: UInt16(1), Array.init)[...])
    XCTAssertEqual(
      RuntimeValue(integer: -1, bitWidth: 16, alignment: 2).bytes,
      withUnsafeBytes(of: UInt16(65535), Array.init)[...])

    XCTAssertEqual(
      RuntimeValue(integer: 1, bitWidth: 32, alignment: 4).bytes,
      withUnsafeBytes(of: UInt32(1), Array.init)[...])

    XCTAssertEqual(
      RuntimeValue(integer: 1, bitWidth: 64, alignment: 8).bytes,
      withUnsafeBytes(of: UInt64(1), Array.init)[...])

    XCTAssertEqual(
      RuntimeValue(integer: 1, bitWidth: 128, alignment: 8).bytes,
      withUnsafeBytes(of: UInt128(1), Array.init)[...])
  }

  func testRuntimeValueBoolInitializer() {
    let f = RuntimeValue(bool: false, havingLayout: .init(alignment: 1, size: 1))
    XCTAssertFalse(f.asBool)
    XCTAssertEqual(f.bytes, [0])

    let t = RuntimeValue(bool: true, havingLayout: .init(alignment: 1, size: 1))
    XCTAssertTrue(t.asBool)
    XCTAssertEqual(t.bytes, [1])
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

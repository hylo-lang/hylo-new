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
    for b in [.little, .big] as [Endianness] {
      XCTAssertEqual(RuntimeValue(integer: 0, bitWidth: 8, byteOrder: b).asI8, 0)
      XCTAssertEqual(RuntimeValue(integer: 1, bitWidth: 8, byteOrder: b).asI8, 1)
      XCTAssertEqual(RuntimeValue(integer: -1, bitWidth: 8, byteOrder: b).asI8, 255)
      XCTAssertEqual(RuntimeValue(integer: -2, bitWidth: 8, byteOrder: b).asI8, 254)

      XCTAssertEqual(
        RuntimeValue(integer: 1, bitWidth: 16, byteOrder: b)
          .asI16(assumingByteOrder: b), 1)
      XCTAssertEqual(
        RuntimeValue(integer: -1, bitWidth: 16, byteOrder: b)
          .asI16(assumingByteOrder: b), UInt16.max)

      XCTAssertEqual(
        RuntimeValue(integer: 1, bitWidth: 32, byteOrder: b)
          .asI32(assumingByteOrder: b), 1)
      XCTAssertEqual(
        RuntimeValue(integer: -1, bitWidth: 32, byteOrder: b)
          .asI32(assumingByteOrder: b), UInt32.max)

      XCTAssertEqual(
        RuntimeValue(integer: 1, bitWidth: 64, byteOrder: b)
          .asI64(assumingByteOrder: b), 1)
      XCTAssertEqual(
        RuntimeValue(integer: -1, bitWidth: 64, byteOrder: b)
          .asI64(assumingByteOrder: b), UInt64.max)
    }
  }

  func testRuntimeValueInitializerFollowsByteOrder() {
    XCTAssertEqual(RuntimeValue(integer: 0, bitWidth: 8, byteOrder: .little).bytes, [0])

    XCTAssertEqual(
      RuntimeValue(integer: 0xff01, bitWidth: 16, byteOrder: .little).bytes, [0x01, 0xff])
    XCTAssertEqual(
      RuntimeValue(integer: 0xff01, bitWidth: 16, byteOrder: .big).bytes, [0xff, 0x01])
  }

  func testRuntimeValueBoolInitializer() {
    let f = RuntimeValue(bool: false)
    XCTAssertFalse(f.asBool)
    XCTAssertEqual(f.bytes, [0])

    let t = RuntimeValue(bool: true)
    XCTAssertTrue(t.asBool)
    XCTAssertEqual(t.bytes, [1])
  }

}

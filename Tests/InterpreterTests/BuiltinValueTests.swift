import FrontEnd
import XCTest

@testable import Interpreter

final class BuiltinValueTests: XCTestCase {

  func testBooleanValueWithLsbFirstOrderingABI() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .lsbFirst))
    XCTAssertEqual(
      BuiltinValue(bool: true).byteRepresentation(as: .i(1), usingLayoutsFrom: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(bool: false).byteRepresentation(as: .i(1), usingLayoutsFrom: &l),
      [0]
    )
  }

  func testBooleanValueWithMsbFirstOrderingABI() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .msbFirst))
    XCTAssertEqual(
      BuiltinValue(bool: true).byteRepresentation(as: .i(1), usingLayoutsFrom: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(bool: false).byteRepresentation(as: .i(1), usingLayoutsFrom: &l),
      [0]
    )
  }

  func testIntegerValue() {
    XCTAssertEqual(BuiltinValue(integer: 0, bitWidth: 8).asI8, 0)
    XCTAssertEqual(BuiltinValue(integer: 1, bitWidth: 8).asI8, 1)
    XCTAssertEqual(BuiltinValue(integer: 127, bitWidth: 8).asI8, 127)
    XCTAssertEqual(BuiltinValue(integer: 255, bitWidth: 8).asI8, 255)
    XCTAssertEqual(BuiltinValue(integer: -1, bitWidth: 8).asI8, 255)
    XCTAssertEqual(BuiltinValue(integer: -2, bitWidth: 8).asI8, 254)
    XCTAssertEqual(BuiltinValue(integer: -128, bitWidth: 8).asI8, 128)
  }

  func testIntegersForLsbFirst() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .lsbFirst))
    XCTAssertEqual(
      BuiltinValue(integer: 2, bitWidth: 8)
        .byteRepresentation(as: .i(8), usingLayoutsFrom: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 16)
        .byteRepresentation(as: .i(16), usingLayoutsFrom: &l),
      [2, 1]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 32)
        .byteRepresentation(as: .i(32), usingLayoutsFrom: &l),
      [2, 1, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 64)
        .byteRepresentation(as: .i(64), usingLayoutsFrom: &l),
      [2, 1, 0, 0, 0, 0, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 128)
        .byteRepresentation(as: .i(128), usingLayoutsFrom: &l),
      [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    )
  }

  func testIntegersForMsbFirst() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .msbFirst))
    XCTAssertEqual(
      BuiltinValue(integer: 2, bitWidth: 8)
        .byteRepresentation(as: .i(8), usingLayoutsFrom: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 16)
        .byteRepresentation(as: .i(16), usingLayoutsFrom: &l),
      [1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 32)
        .byteRepresentation(as: .i(32), usingLayoutsFrom: &l),
      [0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 64)
        .byteRepresentation(as: .i(64), usingLayoutsFrom: &l),
      [0, 0, 0, 0, 0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 128)
        .byteRepresentation(as: .i(128), usingLayoutsFrom: &l),
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
    )
  }

}

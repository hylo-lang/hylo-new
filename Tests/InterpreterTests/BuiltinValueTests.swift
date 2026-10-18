import FrontEnd
import XCTest

@testable import Interpreter

final class BuiltinValueTests: XCTestCase {

  func testBooleanValueWithLsbFirstOrderingABI() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .lsbFirst))
    XCTAssertEqual(
      BuiltinValue(bool: true).byteRepresentation(asValueOf: .i(1), laidOutUsing: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(bool: false).byteRepresentation(asValueOf: .i(1), laidOutUsing: &l),
      [0]
    )
  }

  func testBooleanValueWithMsbFirstOrderingABI() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .msbFirst))
    XCTAssertEqual(
      BuiltinValue(bool: true).byteRepresentation(asValueOf: .i(1), laidOutUsing: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(bool: false).byteRepresentation(asValueOf: .i(1), laidOutUsing: &l),
      [0]
    )
  }

  func testIntegerValue() {
    XCTAssertEqual(BuiltinValue(integer: 0, bitWidth: 8).asUInt8, 0)
    XCTAssertEqual(BuiltinValue(integer: 1, bitWidth: 8).asUInt8, 1)
    XCTAssertEqual(BuiltinValue(integer: 127, bitWidth: 8).asUInt8, 127)
    XCTAssertEqual(BuiltinValue(integer: 255, bitWidth: 8).asUInt8, 255)
    XCTAssertEqual(BuiltinValue(integer: -1, bitWidth: 8).asUInt8, 255)
    XCTAssertEqual(BuiltinValue(integer: -2, bitWidth: 8).asUInt8, 254)
    XCTAssertEqual(BuiltinValue(integer: -128, bitWidth: 8).asUInt8, 128)
  }

  func testIntegersForLsbFirst() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .lsbFirst))
    XCTAssertEqual(
      BuiltinValue(integer: 2, bitWidth: 8)
        .byteRepresentation(asValueOf: .i(8), laidOutUsing: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 16)
        .byteRepresentation(asValueOf: .i(16), laidOutUsing: &l),
      [2, 1]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 32)
        .byteRepresentation(asValueOf: .i(32), laidOutUsing: &l),
      [2, 1, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 64)
        .byteRepresentation(asValueOf: .i(64), laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 128)
        .byteRepresentation(asValueOf: .i(128), laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    )
  }

  func testIntegersForMsbFirst() {
    var l = TypeLayoutCache(for: UnrealABI(byteOrder: .msbFirst))
    XCTAssertEqual(
      BuiltinValue(integer: 2, bitWidth: 8)
        .byteRepresentation(asValueOf: .i(8), laidOutUsing: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 16)
        .byteRepresentation(asValueOf: .i(16), laidOutUsing: &l),
      [1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 32)
        .byteRepresentation(asValueOf: .i(32), laidOutUsing: &l),
      [0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 64)
        .byteRepresentation(asValueOf: .i(64), laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(integer: 258, bitWidth: 128)
        .byteRepresentation(asValueOf: .i(128), laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
    )
  }

}

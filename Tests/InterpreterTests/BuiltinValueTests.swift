import FrontEnd
import XCTest

@testable import Interpreter

final class BuiltinValueTests: XCTestCase {

  func testBooleanValueWithLsbFirstOrderingABI() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .little))
    XCTAssertEqual(
      BuiltinValue(true).bytes(ofStored: .i(1), laidOutUsing: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(false).bytes(ofStored: .i(1), laidOutUsing: &l),
      [0]
    )
  }

  func testBooleanValueWithMsbFirstOrderingABI() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .big))
    XCTAssertEqual(
      BuiltinValue(true).bytes(ofStored: .i(1), laidOutUsing: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(false).bytes(ofStored: .i(1), laidOutUsing: &l),
      [0]
    )
  }

  func testIntegerValue() {
    XCTAssertEqual(BuiltinValue(0, bitWidth: 8).asUInt8, 0)
    XCTAssertEqual(BuiltinValue(1, bitWidth: 8).asUInt8, 1)
    XCTAssertEqual(BuiltinValue(127, bitWidth: 8).asUInt8, 127)
    XCTAssertEqual(BuiltinValue(255, bitWidth: 8).asUInt8, 255)
    XCTAssertEqual(BuiltinValue(-1, bitWidth: 8).asUInt8, 255)
    XCTAssertEqual(BuiltinValue(-2, bitWidth: 8).asUInt8, 254)
    XCTAssertEqual(BuiltinValue(-128, bitWidth: 8).asUInt8, 128)
  }

  func testIntegersForLsbFirst() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .little))
    XCTAssertEqual(
      BuiltinValue(2, bitWidth: 8)
        .bytes(ofStored: .i(8), laidOutUsing: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 16)
        .bytes(ofStored: .i(16), laidOutUsing: &l),
      [2, 1]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 32)
        .bytes(ofStored: .i(32), laidOutUsing: &l),
      [2, 1, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 64)
        .bytes(ofStored: .i(64), laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 128)
        .bytes(ofStored: .i(128), laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    )
  }

  func testIntegersForMsbFirst() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .big))
    XCTAssertEqual(
      BuiltinValue(2, bitWidth: 8)
        .bytes(ofStored: .i(8), laidOutUsing: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 16)
        .bytes(ofStored: .i(16), laidOutUsing: &l),
      [1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 32)
        .bytes(ofStored: .i(32), laidOutUsing: &l),
      [0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 64)
        .bytes(ofStored: .i(64), laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, bitWidth: 128)
        .bytes(ofStored: .i(128), laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
    )
  }

}

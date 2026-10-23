import FrontEnd
import XCTest

@testable import Interpreter

final class BuiltinValueTests: XCTestCase {

  func testBooleanValueWithLsbFirstOrderingABI() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .little))
    XCTAssertEqual(
      BuiltinValue(true).bytes(laidOutUsing: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(false).bytes(laidOutUsing: &l),
      [0]
    )
  }

  func testBooleanValueWithMsbFirstOrderingABI() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .big))
    XCTAssertEqual(
      BuiltinValue(true).bytes(laidOutUsing: &l),
      [1]
    )

    XCTAssertEqual(
      BuiltinValue(false).bytes(laidOutUsing: &l),
      [0]
    )
  }

  func testIntegerValue() {
    XCTAssertEqual(BuiltinValue(0, ofType: .i(8)).i8!, 0)
    XCTAssertEqual(BuiltinValue(1, ofType: .i(8)).i8!, 1)
    XCTAssertEqual(BuiltinValue(127, ofType: .i(8)).i8!, 127)
    XCTAssertEqual(BuiltinValue(255, ofType: .i(8)).i8!, 255)
    XCTAssertEqual(BuiltinValue(-1, ofType: .i(8)).i8!, 255)
    XCTAssertEqual(BuiltinValue(-2, ofType: .i(8)).i8!, 254)
    XCTAssertEqual(BuiltinValue(-128, ofType: .i(8)).i8!, 128)
  }

  func testIntegersForLsbFirst() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .little))
    XCTAssertEqual(
      BuiltinValue(2, ofType: .i(8)).bytes(laidOutUsing: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(16)).bytes(laidOutUsing: &l),
      [2, 1]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(32)).bytes(laidOutUsing: &l),
      [2, 1, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(64)).bytes(laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(128)).bytes(laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .word).bytes(laidOutUsing: &l),
      [2, 1, 0, 0, 0, 0, 0, 0]
    )
  }

  func testIntegersForMsbFirst() {
    var l = LayoutComputer(for: UnrealABI(byteOrder: .big))
    XCTAssertEqual(
      BuiltinValue(2, ofType: .i(8)).bytes(laidOutUsing: &l),
      [2]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(16)).bytes(laidOutUsing: &l),
      [1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(32)).bytes(laidOutUsing: &l),
      [0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(64)).bytes(laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .i(128)).bytes(laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]
    )

    XCTAssertEqual(
      BuiltinValue(258, ofType: .word).bytes(laidOutUsing: &l),
      [0, 0, 0, 0, 0, 0, 1, 2]
    )
  }

}

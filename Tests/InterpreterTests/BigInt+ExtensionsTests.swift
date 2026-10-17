import BigInt
import FrontEnd
import XCTest

@testable import Interpreter

final class BigIntExtensionsTests: XCTestCase {

  func testPositiveNumberIsRepresentable() {
    for i in 0..<256 {
      XCTAssert(BigInt(i).isRepresentable(asIntegerHavingBitWidth: 8))
    }
    for i in 256..<512 {
      XCTAssertFalse(BigInt(i).isRepresentable(asIntegerHavingBitWidth: 8))
    }
  }

  func testNegativeNumberIsRepresentable() {
    for i in -128..<0 {
      XCTAssert(BigInt(i).isRepresentable(asIntegerHavingBitWidth: 8))
    }
    for i in -256 ..< -128 {
      XCTAssertFalse(BigInt(i).isRepresentable(asIntegerHavingBitWidth: 8))
    }
  }

}

import Utilities
import XCTest

final class SequenceTests: XCTestCase {

  func testSortedByKeyPath() {
    let xs = (0 ..< 10).map({ (i) in (a: i, b: 10 - i) })
    XCTAssert(xs.sorted(by: \.b).elementsEqual(xs.reversed(), by: { (a, b) in a == b }))
  }

  func testLeast() {
    let x0: [E] = []
    XCTAssertNil(x0.least(by: E.areInIncreasingOrder(_:_:)))
    let x1: [E] = [.d, .b, .c]
    XCTAssertNil(x1.least(by: E.areInIncreasingOrder(_:_:)))
    let x2: [E] = [.d, .b, .e, .f]
    XCTAssertEqual(x2.least(by: E.areInIncreasingOrder(_:_:)), .f)
  }

  func testMin() {
    let xs = [1, 2, 3, 4]
    XCTAssertEqual(xs.min(by: { (x) in x }), 1)
    XCTAssertEqual(xs.min(by: { (x) in -x }), 4)
  }

}

private enum E: Equatable {

  case a, b, c, d, e, f

  static func areInIncreasingOrder(_ lhs: E, _ rhs: E) -> Bool {
    switch (lhs, rhs) {
    case (_, .a):
      return lhs != .a
    case (_, .b):
      return (lhs == .d) || (lhs == .e) || (lhs == .f)
    case (_, .c):
      return false
    case (_, .d):
      return lhs == .f
    case (_, .e):
      return lhs == .f
    case (_, .f):
      return false
    }
  }

}

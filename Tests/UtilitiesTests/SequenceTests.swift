import Utilities
import XCTest

final class SequenceTests: XCTestCase {

  func testSortedByKeyPath() {
    let xs = (0 ..< 10).map({ (i) in (a: i, b: 10 - i) })
    XCTAssert(xs.sorted(by: \.b).elementsEqual(xs.reversed(), by: { (a, b) in a == b }))
  }

  func testLeast() {
    let x0: [Int] = []
    XCTAssertNil(x0.least(by: StrictOrdering.comparing(\.self)))
    let x1: [Int] = [1, 2, 1, 3]
    XCTAssertNil(x1.least(by: StrictOrdering.comparing(\.self)))
    let x2: [Int] = [1, 2, 0, 3]
    XCTAssertEqual(x2.least(by: StrictOrdering.comparing(\.self)), 0)
  }

  func testMin() {
    let xs = [1, 2, 3, 4]
    XCTAssertEqual(xs.min(measuredBy: { (x) in x }), 1)
    XCTAssertEqual(xs.min(measuredBy: { (x) in -x }), 4)
  }

}

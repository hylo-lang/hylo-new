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

  func testMinimalElements() {
    var g = SeedableRandomNumberGenerator(seed: 0)
    for _ in 1 ..< 1000 {
      let xs = (0 ..< 20).map({ _ in g.next(upperBound: 30 as UInt8) })
      let minimal = xs.minimalElements(
        by: { (x, y) in StrictOrdering(between: x / 3, and: y / 3) })
      let least = xs.min()!

      XCTAssertEqual(
        minimal, xs.filter({ (x) in x / 3 == least / 3 }),
        "input: \(xs)"
      )
    }
  }

}

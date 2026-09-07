import Utilities
import XCTest

final class MutableCollectionTests: XCTestCase {

  func testCompactMapInPlace() {
    var xs = Array(0 ..< 20)
    let ys = xs.compactMap(transform)
    xs.compactMapInPlace(transform)
    XCTAssertEqual(xs, ys)

    func transform(x: Int) -> Int? {
      if (x % 3) == 0 {
        return nil
      } else if (x % 2) == 0 {
        return .some(-x)
      } else {
        return .some(x)
      }
    }
  }

}

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

  func testCopyElements() {
    let source = Array(0..<10)

    var destination = Array(10..<20)
    destination.copyElements(from: source)
    XCTAssertEqual(destination, Array(0..<10))

    destination = Array(10..<15)
    destination.copyElements(from: source)
    XCTAssertEqual(destination, Array(0..<5))

    destination = Array(10..<30)
    destination.copyElements(from: source)
    XCTAssertEqual(destination, Array(0..<10) + Array(20..<30))
  }

}

import Utilities
import XCTest

final class ArrayTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let a = [Int](minimumCapacity: 100)
    XCTAssert(a.capacity >= 100)
  }

  func testInitPrependedTo() {
    let a = Array(0, prependedTo: 1 ..< 10)
    XCTAssert(a.elementsEqual(0 ..< 10))
  }

  func testInitTerminatedBy() {
    let a = Array(0 ..< 9, terminatedBy: 9)
    XCTAssert(a.elementsEqual(0 ..< 10))
  }

  func testAppending() {
    let a = Array(0 ..< 9)
    XCTAssert(a.appending(9).elementsEqual(0 ..< 10))
  }

}

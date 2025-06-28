import StableCollections
import XCTest

class ListTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = List<String>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testInitWithSequence() {
    let members = ["a", "b"]
    let s = List<String>(members)
    XCTAssert(s.elementsEqual(members))
  }

  func testInitWithArrayLiteral() {
    let s: List = ["a", "b"]
    XCTAssert(s.elementsEqual(["a", "b"]))
  }

  func testIsEmpty() {
    var s = List<String>()
    XCTAssert(s.isEmpty)
    s.append("a")
    XCTAssertFalse(s.isEmpty)
  }

  func testCount() {
    var s = List<String>()
    XCTAssertEqual(s.count, 0)
    let a = s.append("a")
    XCTAssertEqual(s.count, 1)
    let b = s.append("b")
    XCTAssertEqual(s.count, 2)
    s.remove(at: a)
    XCTAssertEqual(s.count, 1)
    s.remove(at: b)
    XCTAssertEqual(s.count, 0)
  }

  func testAppend() {
    var s = List<String>()

    _ = s.append("a")
    XCTAssertEqual(Array(s), ["a"])
    let b = s.append("b")
    XCTAssertEqual(Array(s), ["a", "b"])
    _ = s.append("c")
    XCTAssertEqual(Array(s), ["a", "b", "c"])

    s.remove(at: b)
    s.append("d")
    XCTAssertEqual(Array(s), ["a", "c", "d"])
  }

  func testPrepend() {
    var s = List<String>()

    _ = s.prepend("a")
    XCTAssertEqual(Array(s), ["a"])
    let b = s.prepend("b")
    XCTAssertEqual(Array(s), ["b", "a"])
    _ = s.prepend("c")
    XCTAssertEqual(Array(s), ["c", "b", "a"])

    s.remove(at: b)
    s.prepend("d")
    XCTAssertEqual(Array(s), ["d", "c", "a"])
  }

  func testInsertAfter() {
    var s = List<String>()

    let a = s.prepend("a")
    s.insert("b", after: a)
    s.insert("c", after: a)
    XCTAssertEqual(Array(s), ["a", "c", "b"])
  }

  func testInsertBefore() {
    var s = List<String>()

    let a = s.prepend("a")
    s.insert("b", before: a)
    s.insert("c", before: a)
    XCTAssertEqual(Array(s), ["b", "c", "a"])
  }

  func testInsertAt() {
    var s = List<String>()

    s.insert("a", at: s.startIndex)
    s.insert("b", at: s.startIndex)
    s.insert("c", at: s.index(after: s.startIndex))
    XCTAssertEqual(Array(s), ["b", "c", "a"])
  }

  func testReserveCapacity() {
    var s: List = ["a", "b", "c"]
    let t = s
    s.reserveCapacity(100)
    XCTAssertEqual(s, t)
    XCTAssertNotEqual(s.capacity, t.capacity)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

}

import FrontEnd
import XCTest

class IndexPathTests: XCTestCase {

  func testInitWithArrayLiteral() {
    let p: FrontEnd.IndexPath = [1, 2]
    XCTAssert(p.elementsEqual([1, 2]))
    let q: FrontEnd.IndexPath = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    XCTAssert(q.elementsEqual(0 ..< 16))
  }

  func testIsEmpty() {
    var p = FrontEnd.IndexPath()
    XCTAssert(p.isEmpty)
    p.append(1)
    XCTAssertFalse(p.isEmpty)
  }

  func testCount() {
    var p = FrontEnd.IndexPath()
    XCTAssertEqual(p.count, 0)
    for i in 0 ..< 32 {
      p.append(1 & 0xf)
      XCTAssertEqual(p.count, i + 1)
    }
  }

  func testAppend() {
    var p = FrontEnd.IndexPath()

    p.append(0)
    XCTAssert(p.elementsEqual([0]))
    p.append(1)
    XCTAssert(p.elementsEqual([0, 1]))

    for i in 2 ..< 32 {
      p.append(i)
    }
    XCTAssert(p.elementsEqual(0 ..< 32))
  }

  func testAppendContentsOf() {
    var p = FrontEnd.IndexPath()
    p.append(contentsOf: 0 ..< 8)
    XCTAssert(p.elementsEqual(0 ..< 8))
    p.append(contentsOf: 8 ..< 16)
    XCTAssert(p.elementsEqual(0 ..< 16))
  }

  func testIsCollection() {
    var p = FrontEnd.IndexPath()
    var i: Int

    p.append(contentsOf: 0 ..< 8)
    i = p.startIndex
    XCTAssertEqual(p[i], 0)
    i = p.index(after: i)
    XCTAssertEqual(p[i], 1)
    XCTAssertEqual(p.index(i, offsetBy: 7), p.endIndex)

    p.append(contentsOf: 0 ..< 8)
    i = p.index(p.startIndex, offsetBy: 10)
    XCTAssertEqual(p[i], 2)
    i = p.index(after: i)
    XCTAssertEqual(p[i], 3)
    XCTAssertEqual(p.index(i, offsetBy: 5), p.endIndex)
  }

}

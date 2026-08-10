import Utilities
import XCTest

final class SortedDictionaryTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let s = SortedDictionary<Int, String>(minimumCapacity: 100)
    XCTAssertGreaterThanOrEqual(s.capacity, 100)
  }

  func testInitWithDictionaryLiteral() {
    let s: SortedDictionary = [1: "a", 2: "b"]
    XCTAssert(s.keys.elementsEqual([1, 2]))
    XCTAssert(s.values.elementsEqual(["a", "b"]))
  }

  func testMerging() {
    let s0: SortedDictionary = [1: "a", 2: "b", 4: "d", 5: "e"]

    XCTAssert(s0.merging(SortedDictionary(), uniquingKeysWith: +) == s0)
    XCTAssert(SortedDictionary().merging(s0, uniquingKeysWith: +) == s0)

    let s1: SortedDictionary = [1: "a", 2: "b", 3: "c"]
    let s2: SortedDictionary = [2: "b", 6: "f"]

    let t0 = s0.merging(s1, uniquingKeysWith: +)
    XCTAssert(t0.keys.elementsEqual([1, 2, 3, 4, 5]))
    XCTAssert(t0.values.elementsEqual(["aa", "bb", "c", "d", "e"]))

    let t1 = s0.merging(s2, uniquingKeysWith: +)
    XCTAssert(t1.keys.elementsEqual([1, 2, 4, 5, 6]))
    XCTAssert(t1.values.elementsEqual(["a", "bb", "d", "e", "f"]))
  }

}

import XCTest

@testable import FrontEnd

final class TypeStoreTests: XCTestCase {

  func testDemandError() {
    var store = TypeStore()
    let t = ErrorType()
    let i = store.demand(t)
    XCTAssertEqual(i.erased, AnyTypeIdentity.error)
    XCTAssertEqual(store[i], t)
  }

  func testDemandVoid() {
    var store = TypeStore()
    let t = Tuple.empty
    let i = store.demand(t)
    XCTAssertEqual(i.erased, AnyTypeIdentity.void)
    XCTAssertEqual(store[i], t)
  }

  func testDemandVariable() {
    var store = TypeStore()
    let t = TypeVariable(identifier: 123)
    let i = store.demand(t)
    XCTAssertEqual(i.erased, AnyTypeIdentity(variable: 123))
    XCTAssertEqual(store[i], t)
  }

  func testDemandNever() {
    var store = TypeStore()
    let t = store.never()
    let u = store.never()
    XCTAssertEqual(t, u)
  }

  func testDemand() {
    var store = TypeStore()
    let t = Tuple.cons(head: .void, tail: .void)
    let i = store.demand(t)
    XCTAssertEqual(store[i], t)
    let j = store.demand(t)
    XCTAssertEqual(i, j)
  }

}

import FrontEnd
import XCTest

final class DiagnosticSetTests: XCTestCase {

  func testContainsError() {
    var log = DiagnosticSet()
    XCTAssertFalse(log.containsError)

    let f: SourceFile = "Hello."
    log.insert(.init(.error, "bang", at: f.span))
    XCTAssert(log.containsError)
  }

  func testInsert() {
    var log = DiagnosticSet()
    let f: SourceFile = "Hello."
    log.insert(.init(.error, "bang", at: f.span))
    log.insert(.init(.error, "bong", at: f.span))
    log.insert(.init(.error, "bing", at: f.span))
    XCTAssertEqual(log.elements.count, 3)

    log.insert(.init(.error, "bang", at: f.span))
    XCTAssertEqual(log.elements.count, 3)
  }

  func testStringRepresentation() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(.error, "bang", at: s)
    let d = DiagnosticSet(CollectionOfOne(e))

    XCTAssertEqual(
      "\(d)",
      """
      
      virtual:///1ssiyy33rbj6z:1.1-3: error: bang
      Hello.
      ~~

      """)
  }

}

import FrontEnd
import XCTest

final class DiagnosticTests: XCTestCase {

  func testDescription() {
    let f: SourceFile = "Hello."
    let e = Diagnostic(.error, "bang", at: f.span)
    XCTAssertEqual(e.description, "virtual://1ssiyy33rbj6z:1.1-7: error: bang")
  }

  func testRender() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(.error, "bang", at: s)

    var rendered = ""
    e.render(into: &rendered, style: .unstyled)
    XCTAssertEqual(
      rendered,
      """
      virtual://1ssiyy33rbj6z:1.1-3: error: bang
      Hello.
      ~~

      """)
  }

  func testRenderWithNotes() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(
      .error, "bang", at: s,
      notes: [
        .init(.note, "see this", at: .empty(at: .init(f.startIndex, in: f))),
        .init(.note, "and that", at: .empty(at: .init(f.index(after: f.startIndex), in: f))),
      ])

    var rendered = ""
    e.render(into: &rendered, style: .unstyled)
    XCTAssertEqual(
      rendered,
      """
      virtual://1ssiyy33rbj6z:1.1-3: error: bang
      Hello.
      ~~
      virtual://1ssiyy33rbj6z:1.1: note: see this
      Hello.
      ^
      virtual://1ssiyy33rbj6z:1.2: note: and that
      Hello.
       ^

      """)
  }

  func testRenderStyled() {
    let f: SourceFile = "Hello."
    let s = SourceSpan(f.startIndex ..< f.index(f.startIndex, offsetBy: 2), in: f)
    let e = Diagnostic(.error, "bang", at: s)

    var rendered = ""
    e.render(into: &rendered, style: .styled)
    XCTAssertEqual(
      rendered,
      """
      \u{001B}[1mvirtual://1ssiyy33rbj6z:1.1-3\u{001B}[0m: \u{001B}[1m\u{001B}[31merror\u{001B}[0m: \u{001B}[1mbang\u{001B}[0m
      Hello.
      ~~

      """)
  }

}

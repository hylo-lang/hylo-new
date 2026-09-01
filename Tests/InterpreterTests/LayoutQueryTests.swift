import Foundation
import FrontEnd
import XCTest

import Interpreter

final class LayoutQueryTests: XCTestCase {

  /// The program in which queried sources are type checked.
  private var p = Program(forTesting: true)

  func testLayoutsOfTypesDeclared() async throws {
    let (m, _) = await add(
      """
      public struct Pair {
        let x: Builtin.i8
        let y: Builtin.i64
      }
      """)

    var q = LayoutQuery()
    let ls = q.layoutsOfTypesDeclared(in: m, of: &p)

    XCTAssertEqual(ls.count, 1)
    XCTAssertEqual(ls.first?.type, "Pair")
    XCTAssertEqual(ls.first?.size, 9)
    XCTAssertEqual(ls.first?.alignment, 8)
    XCTAssertEqual(ls.first?.isEnum, false)

    // Members are reported in declaration order, at the offsets given by storage order, each
    // pointing at the name the user wrote.
    XCTAssertEqual(
      ls.first?.parts,
      [
        .init(
          name: "x", type: "i8", offset: 8, size: 1, alignment: 1,
          site: .init(line: 2, column: 7, endLine: 2, endColumn: 8)),
        .init(
          name: "y", type: "i64", offset: 0, size: 8, alignment: 8,
          site: .init(line: 3, column: 7, endLine: 3, endColumn: 8)),
      ])
    XCTAssertEqual(ls.first?.site?.line, 1)
  }

  func testLayoutOfEnum() async throws {
    let (m, _) = await add(
      """
      public enum OptionalI16 {
        case some(wrapped: Builtin.i16)
        case none
      }
      """)

    var q = LayoutQuery()
    let ls = q.layoutsOfTypesDeclared(in: m, of: &p)

    XCTAssertEqual(ls.count, 1)
    XCTAssertEqual(ls.first?.isEnum, true)
    XCTAssertEqual(ls.first?.size, 3)
    XCTAssertEqual(ls.first?.parts.last?.name, "discriminator")
    XCTAssertEqual(ls.first?.parts.last?.offset, 2)
  }

  func testLayoutOfTypeAtCursor() async throws {
    let (_, f) = await add(
      """
      // A comment.
      public struct S {
        let a: Builtin.i16
      }
      """)

    var q = LayoutQuery()
    func layout(line: Int, character: Int) -> LayoutDescription? {
      q.layout(ofTypeAt: p[sourceFile: f].index(line: line, utf16Offset: character), in: f, of: &p)
    }

    // A cursor on a type expression describes the type it denotes. It is not declared here, so
    // it carries no region for this source.
    XCTAssertEqual(layout(line: 2, character: 17)?.type, "i16")
    XCTAssertEqual(layout(line: 2, character: 17)?.size, 2)
    XCTAssertNil(layout(line: 2, character: 17)?.site)

    // A cursor on a declaration describes the type it declares.
    XCTAssertEqual(layout(line: 1, character: 14)?.type, "S")

    // A cursor on no tree at all describes nothing.
    XCTAssertNil(layout(line: 0, character: 3))
  }

  func testTypesWithoutLayoutAreOmitted() async throws {
    let (m, _) = await add(
      """
      public trait T {}
      public struct Generic<X> { let x: X }
      """)

    var q = LayoutQuery()
    XCTAssert(q.layoutsOfTypesDeclared(in: m, of: &p).isEmpty)
  }

  func testSerialScopingAgreesWithConcurrentScoping() async throws {
    let source = """
      public struct Pair {
        let x: Builtin.i8
        let y: Builtin.i64
      }
      public enum Choice {
        case some(wrapped: Builtin.i16)
        case none
      }
      """

    let (m, _) = await add(source)
    var concurrent = LayoutQuery()
    let expected = concurrent.layoutsOfTypesDeclared(in: m, of: &p)
    XCTAssertEqual(expected.count, 2)

    var q = Program(forTesting: true)
    let n = q.demandModule(.init(UUID().uuidString))
    _ = q[n].addSource(SourceFile(contents: source))
    q.assignScopesSerially(n)
    q.assignTypes(n) { (_, _) in false }

    var serial = LayoutQuery()
    XCTAssertEqual(serial.layoutsOfTypesDeclared(in: n, of: &q), expected)
  }

  /// Adds `s` to `p` as a module of its own, type checks it, and returns their identities.
  private func add(_ s: String) async -> (Module.ID, SourceFile.ID) {
    let m = p.demandModule(.init(UUID().uuidString))
    let f = p[m].addSource(SourceFile(contents: s)).identity
    await p.assignScopes(m)
    p.assignTypes(m) { (_, _) in false }
    return (m, f)
  }

}

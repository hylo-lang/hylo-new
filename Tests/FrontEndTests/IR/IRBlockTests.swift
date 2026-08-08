@testable import FrontEnd
import XCTest

final class IRBlockTests: XCTestCase {

  func testIterator() {
    var p = Program(forTesting: true)
    _ = p.addUserModule(named: "test", source: "@_symbol(f) @extern fun f()")
    let d = p.castUnchecked(p.select(.symbol("f")).uniqueElement!, to: FunctionDeclaration.self)
    var f = IRFunction(
      name: .lowered(.init(d)),
      anchor: p.anchor(at: p[d].site, in: p.parent(containing: d)),
      output: .indirect,
      typeParameters: [],
      termParameters: [.init(type: .void, access: .set, declaration: nil)])

    let entry = f.addBlock()
    let s = IRAlloca(
      staticallySized: .void, alignment: .preferred,
      anchor: p.anchor(at: p[d].site, in: .init(node: d)))

    let x0 = f.insert(s, at: .start(of: entry))
    let x1 = f.insert(s, at: .after(x0))
    let x2 = f.insert(s, at: .after(x1))

    XCTAssertEqual(Array(f.instructions(in: entry)), [x0, x1, x2])
    XCTAssertEqual(Array(f.instructions(in: entry).reversed()), [x2, x1, x0])
  }

}

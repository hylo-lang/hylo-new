import XCTest

@testable import FrontEnd

final class TmpNestedChainTests: XCTestCase {

  func testWrapperTags() async {
    var p = await Program.withMinimalStandardLibrary()
    _ = p.addUserModule(named: "M0", source: "fun g(z: Bool) -> Int { Int() }")
    p = await p.typeChecked()
    let m = p.modules.values.first(where: { $0.name.description == "M0" })!.identity
    var g: DeclarationIdentity? = nil
    for s in p[m].syntax where p.tag(of: s) == FunctionDeclaration.self {
      g = DeclarationIdentity(uncheckedFrom: s)
    }
    let names: [(String, IRFunction.Name)] = [
      ("applied(existentialized(g), 36)", .applied(.existentialized(.lowered(g!)), 36)),
      ("applied(existentialized(g), 46)", .applied(.existentialized(.lowered(g!)), 46)),
      ("slide(slide(g, 5), 36)", .slide(.slide(.lowered(g!), 5), 36)),
      ("slide(slide(g, 36), 46)", .slide(.slide(.lowered(g!), 36), 46)),
      ("slide(synthesized(g, []), 51)", .slide(.synthesized(g!, TypeArguments()), 51)),
      ("slide(g, 36)", .slide(.lowered(g!), 36)),
    ]
    for (label, n) in names {
      let s = p.mangled(n)
      print("\(label): \(s) -> \(DemangledSymbol(s))")
    }
  }
}

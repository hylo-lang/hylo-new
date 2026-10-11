import XCTest

@testable import FrontEnd

/// Tests that demangling recovers the structure of mangled symbols.
final class ManglingAmbiguityTests: XCTestCase {

  /// Tests that each declaration of `program` demangles to the declaration containing it,
  /// qualified by one more component.
  func testDeclarationNames() async {
    let (p, m0) = await typeChecked(program + labels)
    var demangled: [AnySyntaxIdentity: DemangledEntity] = [:]
    for n in p.select(from: m0, .satisfies({ (n) in p.isDeclaration(n) })) {
      demangled[n] = entity(p.mangled(DeclarationIdentity(uncheckedFrom: n)))
    }

    for (n, e) in demangled {
      guard let parent = p.parent(containing: n).node.flatMap({ (s) in demangled[s] }) else {
        continue
      }
      guard case .qualified(_, let q) = e else {
        XCTFail("expected a qualified entity, got: \(e)")
        continue
      }
      XCTAssertEqual(q, parent, "(demangled: \(e))")
    }
  }

  /// Tests that IR function names wrapping other names demangle to the demangling of the names
  /// they wrap, for every kind of name, wrapped at most twice, with a range of tags.
  func testWrappedFunctionNames() async {
    let (p, m0) = await typeChecked(program)
    let greet = p.findDeclaration(FunctionDeclaration.self, named: "Greeter.greet", in: m0)!
    let c = p.firstDeclaration(ConformanceDeclaration.self, in: m0)!
    let g = p.findDeclaration(FunctionDeclaration.self, in: m0) { $0.hasPrefix("g") }!
    let origin = p.firstDeclaration(BindingDeclaration.self, in: m0)!

    let bases: [IRFunction.Name] = [
      .lowered(g),
      .initializer(origin),
      .synthesized(g, TypeArguments()),
      .implementation(greet, c, TypeArguments()),
    ]

    // Each way of wrapping a name, paired with the entity that the result should demangle to,
    // given the entity that the wrapped name demangles to.
    typealias Wrapper = (
      name: (IRFunction.Name, Int) -> IRFunction.Name,
      entity: (DemangledEntity, Int) -> DemangledEntity
    )
    let wrappers: [Wrapper] = [
      ({ (n, _) in .existentialized(n) }, { (e, _) in .existentialized(e) }),
      ({ (n, i) in .slide(n, i) }, { (e, i) in .slide(e, i) }),
      ({ (n, i) in .plateau(n, i) }, { (e, i) in .plateau(e, i) }),
      ({ (n, i) in .applied(n, i) }, { (e, i) in .applied(e, i) }),
    ]

    for b in bases {
      guard let e = entity(p.mangled(b)) else { continue }
      for i in 0 ..< 128 {
        for w in wrappers {
          let n = w.name(b, i)
          guard let f = entity(p.mangled(n)) else { continue }
          XCTAssertEqual(f, w.entity(e, i), "\(n)")
          for v in wrappers {
            XCTAssertEqual(entity(p.mangled(v.name(n, i))), v.entity(f, i), "\(v.name(n, i))")
          }
        }
      }
    }
  }

  /// A program declaring a variety of entities.
  private var program: String {
    """
      // Functions returning user-defined and built-in types.
      struct A { public memberwise init }
      struct B { fun f(y: Int) -> A { A() } }
      fun g(z: Bool) -> Int { Int() }

      // A generic extension.
      trait Q {}
      extension <T is Q> T { fun h() {} }

      // A generic conformance with several constraints.
      trait P {}
      struct C<T, U> {}
      trait Greeter { fun greet() }
      given <T is P, U is Q> => C<T, U> is Greeter { fun greet() {} }

      let origin = Int()

      """
  }

  /// Declarations of functions whose parameter labels have various lengths and initial letters,
  /// using the struct `A` declared in `program`.
  private var labels: String {
    var source = ""
    for (i, l) in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".enumerated() {
      for n in 1 ... 120 {
        source += "fun k\(i)_\(n)(a: A, \(l)\(String(repeating: "x", count: n - 1)) b: A) {}\n"
      }
    }
    return source
  }

  /// Returns a type checked program containing `source` in a module named `M0`, along with the
  /// identity of that module.
  private func typeChecked(_ source: String) async -> (Program, Module.ID) {
    var p = await Program.withMinimalStandardLibrary()
    let m0 = p.addUserModule(named: "M0", source: .init(contents: source))
    p = await p.typeChecked()
    failIfContainsError(p)
    return (p, m0)
  }

  /// Returns the entity demangled from `m`, failing the current test if `m` does not demangle to
  /// an entity without error.
  private func entity(
    _ m: String, file: StaticString = #filePath, line: UInt = #line
  ) -> DemangledEntity? {
    assertDemanglingIsOk(mangled: m, file: file, line: line)
    if case .entity(let e) = DemangledSymbol(m) {
      return e
    } else {
      XCTFail("expected an entity, got: \(DemangledSymbol(m))", file: file, line: line)
      return nil
    }
  }

}

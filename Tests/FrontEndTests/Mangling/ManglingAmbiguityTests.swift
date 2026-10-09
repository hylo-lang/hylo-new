import XCTest

@testable import FrontEnd

/// Reproducers for mangled symbols in which the end of a declaration chain is ambiguous.
///
/// After demangling a component, `takeEntity` continues the current qualification chain if the
/// next characters read as an entity operator (other than `R`, `M`, or `rK`). Each test below
/// exercises one situation in which the mangler writes such characters right after the end of a
/// declaration, without a `declarationEnd` separating them.
///
/// Most of these symbols demangle without any error but into the wrong structure, so the tests
/// check the shape of the demangled symbol rather than the absence of `#!`.
final class ManglingAmbiguityTests: XCTestCase {

  /// A function whose signature ends with a nominal type mangled for the first time, followed by
  /// a component nested in that function.
  ///
  /// `…F f lT… sT K1 S3A P3y`: the chain of `A` (in the output type) swallows `P3y`.
  func testDeclarationAfterFunctionReturningNominalType() async {
    let p = await typeChecked(
      """
      struct A { public memberwise init }
      struct B { fun f(y: Int) -> A { A() } }
      """)
    let y = findDeclaration(ParameterDeclaration.self, in: p) { $0.hasSuffix(".y") }!
    assertInnermostComponent(of: p.mangled(y), is: .scope("y"))
  }

  /// Same as above with a reserved type: `R x` does not end a chain either.
  ///
  /// `…F g lT… sT R2 P3z`: the chain of `Int` (in the output type) swallows `P3z`.
  func testDeclarationAfterFunctionReturningReservedType() async {
    let p = await typeChecked(
      """
      fun g(z: Bool) -> Int { Int() }
      """)
    let z = findDeclaration(ParameterDeclaration.self, in: p) { $0.hasSuffix(".z") }!
    assertInnermostComponent(of: p.mangled(z), is: .scope("z"))
  }

  /// An entity operator written immediately after a declaration.
  ///
  /// `mF <greet> cD …`: the chain of `greet` swallows the conformance.
  func testImplementationName() async {
    let p = await typeChecked(
      """
      struct Robot { public memberwise init }
      trait Greeter { fun greet() }
      given Robot is Greeter { fun greet() {} }
      """)
    let greet = findDeclaration(FunctionDeclaration.self, in: p) { $0 == "Greeter.greet" }!
    let c = ConformanceDeclaration.ID(
      uncheckedFrom: findDeclaration(ConformanceDeclaration.self, in: p) { _ in true }!.erased)

    let m = p.mangled(IRFunction.Name.implementation(greet, c, TypeArguments()))
    guard
      case .entity(.implementation(let e, .conformanceDeclaration(_, let usings), let a)) =
        DemangledSymbol(m)
    else {
      return XCTFail("expected an implementation, got: \(DemangledSymbol(m))\n(mangled: \(m))")
    }
    XCTAssertEqual(innermostName(of: e), "greet", "(mangled: \(m))")
    XCTAssertEqual(usings.count, 0, "(mangled: \(m))")
    XCTAssertEqual(a.count, 0, "(mangled: \(m))")
  }

  /// A using of a conformance followed by another using starting with a lookup.
  ///
  /// The usings of the conformance are mangled twice in the name of an implementation: once in the
  /// qualification of `greet` and once for the conformance itself. The second time, each using is
  /// recorded and mangled as `K n`, so the first using swallows the second one. Note that this
  /// symbol is also affected by `testImplementationName` and
  /// `testDeclarationAfterLastUsing`.
  func testUsingFollowedByLookup() async {
    let p = await typeChecked(
      """
      trait P {}
      trait Q {}
      struct A<T, U> {}
      trait Greeter { fun greet() }
      given <T is P, U is Q> => A<T, U> is Greeter { fun greet() {} }
      """)
    let greet = findDeclaration(FunctionDeclaration.self, in: p) {
      $0.hasPrefix("$<ConformanceDeclaration") && $0.hasSuffix(".greet")
    }!
    let c = ConformanceDeclaration.ID(
      uncheckedFrom: findDeclaration(ConformanceDeclaration.self, in: p) { _ in true }!.erased)

    let m = p.mangled(IRFunction.Name.implementation(greet, c, TypeArguments()))
    guard
      case .entity(.implementation(_, .conformanceDeclaration(_, let usings), _)) =
        DemangledSymbol(m)
    else {
      return XCTFail("expected an implementation, got: \(DemangledSymbol(m))\n(mangled: \(m))")
    }
    XCTAssertEqual(usings.count, 2, "(mangled: \(m))")
  }

  /// The last using of an extension followed by the next component of the enclosing chain.
  ///
  /// `…xD <type> 1 rK cD… 0 F f …`: the chain of the using swallows `F f`.
  func testDeclarationAfterLastUsing() async {
    let p = await typeChecked(
      """
      trait Q {}
      extension <T is Q> T { fun f() {} }
      """)
    let f = findDeclaration(FunctionDeclaration.self, in: p) { $0.hasSuffix("f") }!
    assertInnermostName(of: p.mangled(f), is: "f")
  }

  /// An integer written after a declaration whose encoding starts with an entity operator.
  ///
  /// The tag of a slide is written right after the function. 36 is `A` (type alias declaration),
  /// 46 is `K` (lookup), and 51...114 start with `P` (parameter declaration).
  func testIntegerAfterDeclaration() async {
    let p = await typeChecked(
      """
      fun g(z: Bool) -> Int { Int() }
      """)
    let g = findDeclaration(FunctionDeclaration.self, in: p) { $0.hasPrefix("g") }!

    for i in [0, 10, 35, 36, 38, 41, 42, 46, 50, 51, 114, 115] {
      let m = p.mangled(IRFunction.Name.slide(.lowered(g), i))
      guard case .entity(.slide(let e, let j)) = DemangledSymbol(m) else {
        XCTFail("tag \(i): expected a slide, got: \(DemangledSymbol(m))\n(mangled: \(m))")
        continue
      }
      XCTAssertEqual(j, i, "(mangled: \(m))")
      XCTAssertEqual(innermostName(of: e), "g", "tag \(i) (mangled: \(m))")
    }
  }

  /// A string written after a declaration whose length and first character read as an entity
  /// operator.
  ///
  /// The label `Fabcdefgh` has length 9, encoded as `b`, so it would read as `bF` (function
  /// bundle declaration). This case is guarded by `declarationEnd` and is expected to pass.
  func testStringAfterDeclaration() async {
    let p = await typeChecked(
      """
      struct A { public memberwise init }
      fun k(a: A, Fabcdefgh b: Int) {}
      """)
    let k = findDeclaration(FunctionDeclaration.self, in: p) { $0.hasPrefix("k") }!
    let m = p.mangled(k)
    guard
      case .entity(let e) = DemangledSymbol(m),
      case .functionDeclaration(_, .arrow(_, _, _, let inputs, _), _) = components(of: e).last!
    else {
      return XCTFail("expected a function, got: \(DemangledSymbol(m))\n(mangled: \(m))")
    }
    XCTAssertEqual(inputs.map(\.label), [nil, "Fabcdefgh"], "(mangled: \(m))")
  }

  // MARK: Helpers

  /// Returns a type checked program containing `source` in a module named `M0`.
  private func typeChecked(_ source: SourceFile) async -> Program {
    var p = await Program.withMinimalStandardLibrary()
    _ = p.addUserModule(named: "M0", source: source)
    p = await p.typeChecked()
    if p.containsError {
      XCTFail("Unexpected error(s) in test program: \(p.diagnostics)")
    }
    return p
  }

  /// Returns the first declaration of type `t` in `M0` whose debug name satisfies `predicate`.
  private func findDeclaration<T: Syntax>(
    _ t: T.Type, in p: Program, nameMatching predicate: (String) -> Bool
  ) -> DeclarationIdentity? {
    let m = p.modules.values.first(where: { (m) in m.name.description == "M0" })!.identity
    for s in p[m].syntax where p.tag(of: s) == SyntaxTag(t) && p.isDeclaration(s) {
      let d = DeclarationIdentity(uncheckedFrom: s)
      if predicate(p.debugName(of: d)) { return d }
    }
    return nil
  }

  /// Returns the components of the qualification chain `e`, from outermost to innermost.
  private func components(of e: DemangledEntity) -> [DemangledEntity] {
    if case .qualified(let h, let q) = e {
      return components(of: q) + [h]
    } else {
      return [e]
    }
  }

  /// Returns the name of the innermost component of `e` if it is a function declaration.
  private func innermostName(of e: DemangledEntity) -> String? {
    if case .functionDeclaration(let n, _, _) = components(of: e).last! {
      return n.identifier
    } else {
      return nil
    }
  }

  /// Asserts that `m` demangles to an entity whose innermost component is `expected`.
  private func assertInnermostComponent(
    of m: String, is expected: DemangledEntity,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    guard case .entity(let e) = DemangledSymbol(m) else {
      return XCTFail(
        "expected an entity, got: \(DemangledSymbol(m))\n(mangled: \(m))", file: file, line: line)
    }
    XCTAssertEqual(
      components(of: e).last, expected, "demangled: \(e)\n(mangled: \(m))", file: file, line: line)
  }

  /// Asserts that `m` demangles to an entity whose innermost component is a function named `n`.
  private func assertInnermostName(
    of m: String, is n: String, file: StaticString = #filePath, line: UInt = #line
  ) {
    guard case .entity(let e) = DemangledSymbol(m) else {
      return XCTFail(
        "expected an entity, got: \(DemangledSymbol(m))\n(mangled: \(m))", file: file, line: line)
    }
    XCTAssertEqual(
      innermostName(of: e), n, "demangled: \(e)\n(mangled: \(m))", file: file, line: line)
  }

}

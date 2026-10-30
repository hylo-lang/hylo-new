import XCTest

@testable import FrontEnd

/// Tests that demangling recovers the structure of mangled symbols.
///
/// Getting the end of a declaration chain wrong typically produces symbols that demangle without
/// any error but into the wrong structure. Hence, these tests compare demangled symbols with the
/// program from which they have been mangled rather than checking for the absence of `#!`.
final class ManglingAmbiguityTests: XCTestCase {

  /// Tests that each declaration of `program` demangles to a qualified name whose components
  /// describe the scopes containing that declaration.
  func testDeclarationNames() async {
    let (p, m0) = await typeCheckedWithMinimalStandardLibrary(.init(contents: program + labels))
    for n in p.select(from: m0, .satisfies({ (n) in p.isDeclaration(n) })) {
      let d = DeclarationIdentity(uncheckedFrom: n)
      let m = p.mangled(d)
      guard let e = entity(m) else { continue }
      XCTAssert(
        qualifiedName(e, describes: d, relativeTo: nil, in: p),
        "demangling of \(p.debugName(of: d)) has the wrong structure: \(e)\n(mangled: \(m))")
    }
  }

  /// Tests that IR function names demangle to the entities they denote, for every kind of name,
  /// wrapped at most twice, with a range of tags.
  func testWrappedFunctionNames() async {
    let (p, m0) = await typeCheckedWithMinimalStandardLibrary(.init(contents: program))
    let g = p.findDeclaration(FunctionDeclaration.self, in: m0) { $0.hasPrefix("g(") }!
    let origin = p.firstDeclaration(BindingDeclaration.self, named: "origin", in: m0)!
    let greet = p.findDeclaration(FunctionDeclaration.self, in: m0) {
      $0.hasPrefix("$<ConformanceDeclaration") && $0.hasSuffix(".greet")
    }!
    let c = p.cast(p.parent(containing: greet).node!, to: ConformanceDeclaration.self)!

    // The usings of `c` are mangled twice in the name of its implementation of `greet`: once in
    // the qualification of `greet` and once for `c` itself.
    XCTAssertEqual(p[c].contextParameters.usings.count, 2)

    // Each base name, paired with a predicate that checks if the given demangled entity corresponds to it.
    let bases: [(IRFunction.Name, (DemangledEntity) -> Bool)] = [
      (.lowered(g), { (e) in self.qualifiedName(e, describes: g, relativeTo: nil, in: p) }),
      (
        .initializer(origin),
        { (e) in
          guard case .initializer(let x) = e else { return false }
          return self.qualifiedName(x, describes: .init(origin), relativeTo: nil, in: p)
        }
      ),
      (
        .synthesized(g, TypeArguments()),
        { (e) in
          guard case .synthesizedFunction(let x, []) = e else { return false }
          return self.qualifiedName(x, describes: g, relativeTo: nil, in: p)
        }
      ),
      (
        .implementation(greet, c, TypeArguments()),
        { (e) in
          guard case .implementation(let x, let y, []) = e else { return false }
          return self.qualifiedName(x, describes: greet, relativeTo: nil, in: p)
            && self.component(y, describes: .node(c.erased), in: p)
        }
      ),
    ]

    // Single-character tags (some of which read as entity operators), and tags at the boundaries
    // of the variable-length integer encoding.
    let tags = Array(0 ..< 64) + [114, 115, 4209, 4210, 1 << 20]

    // Tags with which wrappers are nested, so that nested wrappers are distinguishable.
    let nestedTags = [0, 9, 10, 36, 46, 51, 115]

    for (b, isExpected) in bases {
      let m = p.mangled(b)
      guard let e = entity(m) else { continue }
      XCTAssert(isExpected(e), "demangling of \(b) has the wrong structure: \(e)\n(mangled: \(m))")

      for w in wrappers(tags: tags) {
        assertDemangling(of: w.name(b), is: w.entity(e), in: p)
      }

      for v in wrappers(tags: nestedTags) {
        for w in wrappers(tags: nestedTags) where (v.tag == nil) || (v.tag != w.tag) {
          assertDemangling(of: w.name(v.name(b)), is: w.entity(v.entity(e)), in: p)
        }
      }
    }
  }

  /// A way of wrapping an IR function name, paired with the way it wraps the entity to which the
  /// wrapped name demangles, and the tag it uses, if any.
  private typealias Wrapper = (
    name: (IRFunction.Name) -> IRFunction.Name,
    entity: (DemangledEntity) -> DemangledEntity,
    tag: Int?
  )

  /// Returns every way of wrapping an IR function name, using the tags in `tags`.
  private func wrappers(tags: [Int]) -> [Wrapper] {
    var result: [Wrapper] = [({ .existentialized($0) }, { .existentialized($0) }, nil)]
    for i in tags {
      result.append(({ .slide($0, i) }, { .slide($0, i) }, i))
      result.append(({ .plateau($0, i) }, { .plateau($0, i) }, i))
      result.append(({ .applied($0, i) }, { .applied($0, i) }, i))
    }
    return result
  }

  /// A program declaring a variety of entities.
  private var program: String {
    """
    // Functions returning user-defined and built-in types.
    struct A { public memberwise init }
    struct B { fun f(y: Int) -> A { A() } }
    fun g(z: Bool) -> Int { Int() }
    static fun s(x: Int) -> Bool { Bool() }

    // Other nominal types and their members.
    enum E<T> {
      case one
      case two(x: T)
    }
    trait W { type X }
    given Void is W { type X = Void }
    type Number = A

    // A generic extension.
    trait Q {}
    extension <T is Q> T { fun h() {} }
    extension <T> {Void, T} { fun i() {} }

    // A generic conformance with several constraints.
    trait P {}
    struct C<T, U> {}
    trait Greeter { fun greet() }
    given <T is P, U is Q> => C<T, U> is Greeter { fun greet() {} }

    // A function bundle.
    public fun project(x: inout Int64) auto -> Int64 {
      let   { (Int64(), ) }
      inout { Int64() }
    }

    // Local declarations and anonymous scopes.
    fun local() {
      let x = Int()
      _ = x
      let f0 = fun[](a: Void) -> Void {
        let b = Int()
        _ = b
      }
      if Bool() {
        let c = Int()
        _ = c
      }
      struct U { fun hammer() {} }
      given Number is Q {}
    }

    let origin = Int()

    """
  }

  /// Declarations of functions with a parameter labeled so that the mangled length of the label,
  /// possibly followed by its first characters, reads as an operator continuing a declaration
  /// chain, right after the mangling of the struct `A` declared in `program`.
  private var labels: String {
    var source = ""
    var seen = Set<[String]>()
    for n in 1 ... 120 {
      // Strings are mangled with their length plus two.
      let d = "\(Base64VarUInt(n + 2))"
      for o in ManglingOperator.entityOperators where !o.endsDeclarationChain {
        let prefix: String
        if o.rawValue.hasPrefix(d) {
          prefix = String(o.rawValue.dropFirst(d.count))
        } else if d.hasPrefix(o.rawValue) {
          prefix = ""
        } else {
          continue
        }

        if (prefix.count > n) || !seen.insert([o.rawValue, prefix, "\(d.count)"]).inserted {
          continue
        }
        let l = prefix + String(repeating: "x", count: n - prefix.count)
        source += "fun k\(n)\(o)(a: A, \(l) b: A) {}\n"
      }
    }
    return source
  }

  /// Returns `true` iff `e` is a qualified name whose components describe `d` and the scopes
  /// containing it, assuming that a relative reference designates `r`.
  private func qualifiedName(
    _ e: DemangledEntity, describes d: DeclarationIdentity, relativeTo r: ScopeIdentity?,
    in p: Program
  ) -> Bool {
    var expected: [Component] = [.node(d.erased)]
    for s in p.scopes(from: p.parent(containing: d)) {
      expected.append(s.node.map(Component.node) ?? .file(s.file))
    }
    expected.append(.module(p.parent(containing: d).module))
    expected.reverse()

    var actual = components(of: e)
    if actual.first == .relative {
      guard let i = r.flatMap({ (s) in expected.firstIndex(of: .node(s.node!)) }) else {
        return false
      }
      expected.removeFirst(i + 1)
      actual.removeFirst()
    }

    return (actual.count == expected.count)
      && zip(actual, expected).allSatisfy({ (a, x) in component(a, describes: x, in: p) })
  }

  /// A component of a qualified name.
  private enum Component: Equatable {

    /// A module.
    case module(Module.ID)

    /// A source file.
    case file(SourceFile.ID)

    /// A scope or declaration.
    case node(AnySyntaxIdentity)

  }

  /// Returns `true` iff `a` describes `x`.
  private func component(_ a: DemangledEntity, describes x: Component, in p: Program) -> Bool {
    switch x {
    case .module(let m):
      return a == .module(p[m].name.description)

    case .file(let f):
      switch p[f].source.name {
      case .local(let u):
        return a == .sourceFile(u.deletingPathExtension().lastPathComponent)
      case .virtual(let u):
        return a == .virtualSourceFile(u.absoluteString)
      }

    case .node(let n):
      return component(a, describes: n, in: p)
    }
  }

  /// Returns `true` iff `a` describes `n`, which is a scope or a declaration.
  private func component(
    _ a: DemangledEntity, describes n: AnySyntaxIdentity, in p: Program
  ) -> Bool {
    switch p.tag(of: n) {
    case Block.self, If.self:
      return a == .anonymousScope(UInt64(n.bits))

    case BindingDeclaration.self:
      let b = BindingDeclaration.ID(uncheckedFrom: n)
      guard case .binding(let names) = a else { return false }
      return names.map(\.identifier) == p.names(introducedBy: b).map(\.identifier)

    case ConformanceDeclaration.self:
      guard case .conformanceDeclaration(_, let usings) = a else { return false }
      let c = ConformanceDeclaration.ID(uncheckedFrom: n)
      return self.usings(usings, describe: p[c].contextParameters.usings, of: n, in: p)

    case ExtensionDeclaration.self:
      guard case .extensionDeclaration(_, let usings) = a else { return false }
      let x = ExtensionDeclaration.ID(uncheckedFrom: n)
      return self.usings(usings, describe: p[x].contextParameters.usings, of: n, in: p)

    case FunctionDeclaration.self:
      let f = FunctionDeclaration.ID(uncheckedFrom: n)
      guard let expected = p.name(of: f) else { return a == .anonymousScope(UInt64(n.bits)) }
      guard
        case .functionDeclaration(let name, let t, let isStatic) = a,
        let inputs = arrowInputs(t)
      else { return false }
      let labels = p[f].parameters.map({ (x) in p[x].label?.value })
      return (name.identifier == expected.identifier) && (name.notation == expected.notation)
        && (isStatic == p.isStatic(f)) && (inputs.suffix(labels.count).map(\.label) == labels)

    case FunctionBundleDeclaration.self:
      let f = FunctionBundleDeclaration.ID(uncheckedFrom: n)
      guard case .functionBundleDeclaration(let name, _) = a else { return false }
      return name.identifier == p.name(of: f).identifier

    case VariantDeclaration.self:
      return a == .variant(p[VariantDeclaration.ID(uncheckedFrom: n)].effect.value)

    default:
      let d = DeclarationIdentity(uncheckedFrom: n)
      return p.name(of: d).map({ (x) in a == .scope(x.identifier) }) ?? false
    }
  }

  /// Returns `true` iff `usings` describe `expected`, which are the usings of `n`.
  private func usings(
    _ usings: [DemangledEntity], describe expected: [DeclarationIdentity],
    of n: AnySyntaxIdentity, in p: Program
  ) -> Bool {
    let s = ScopeIdentity(uncheckedFrom: n)
    return (usings.count == expected.count)
      && zip(usings, expected).allSatisfy({ (u, d) in
        qualifiedName(u, describes: d, relativeTo: s, in: p)
      })
  }

  /// Returns the parameters of `t` if it is an arrow, possibly under universal quantification
  /// and implication.
  private func arrowInputs(_ t: DemangledType) -> [DemangledType.Parameter]? {
    switch t {
    case .arrow(_, _, _, let inputs, _):
      return inputs
    case .universalType(_, let h), .implication(_, let h):
      return arrowInputs(h)
    default:
      return nil
    }
  }

  /// Returns the components of the qualified name `e`, from outermost to innermost.
  private func components(of e: DemangledEntity) -> [DemangledEntity] {
    if case .qualified(let h, let q) = e {
      return components(of: q) + [h]
    } else {
      return [e]
    }
  }

  /// Asserts that `n` demangles to `expected`.
  private func assertDemangling(
    of n: IRFunction.Name, is expected: DemangledEntity, in p: Program,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    let m = p.mangled(n)
    guard let e = entity(m, file: file, line: line) else { return }
    XCTAssertEqual(
      e, expected, "demangling of \(n) is incorrect\n(mangled: \(m))", file: file, line: line)
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
      XCTFail(
        "expected an entity, got: \(DemangledSymbol(m))\n(mangled: \(m))", file: file, line: line)
      return nil
    }
  }

}

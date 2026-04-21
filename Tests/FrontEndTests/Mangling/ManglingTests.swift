import OrderedCollections
import XCTest

@testable import FrontEnd

/// A collection of tests that checks mangling/demangling logic.
final class ManglingTests: XCTestCase {

  /// Tests the mangling and demangling of all kinds of types.
  func testTypes() async {
    var p = await TestProgram()

    let m0 = p.addModule(
      named: "M0",
      source:
        """
        public struct A {}

        public trait Provider {
          type Output
        }

        public struct C {
          type Output = Int
        }

        enum MyEnum<T> {
          case one()
          case two(x: sink T)
        }
        """)
    await p.typeCheck(m0)

    testReservedTypesMangling(program: &p.base)
    testCoreTypesMangling(program: &p.base)
    testArrowTypeMangling(program: &p.base)
    testAssociatedTypeMangling(module: m0, program: &p.base)
    testEnumTypeMangling(module: m0, program: &p.base)
    testEqualityWitnessMangling(program: &p.base)
    testFunctionPointerMangling(program: &p.base)
    testGenericParameterMangling(module: m0, program: &p.base)
    testImplicationTypeMangling(program: &p.base)
    testLiteralTypeMangling(program: &p.base)
    testMachineTypeMangling(program: &p.base)
    testMetakindTypeMangling(program: &p.base)
    testOpaqueEnvironmentTypeMangling(module: m0, program: &p.base)
    testRemoteTypeMangling(program: &p.base)
    testStructTypeMangling(module: m0, program: &p.base)
    testTraitTypeMangling(module: m0, program: &p.base)
    testTupleTypeMangling(program: &p.base)
    testTypeApplicationMangling(module: m0, program: &p.base)
    testUniversalTypeMangling(program: &p.base)
    testTypeAliasMangling(module: m0, program: &p.base)
  }

  /// Tests the mangling and demangling of specific declarations.
  func testSpecificDeclarations() async {
    var p = await TestProgram()

    let m0 = p.addModule(
      named: "M0",
      source:
        """
        trait W { type X }

        given Void is W { type X = Void }

        enum MyEnum<T> {
          case one()
          case two(x: sink T)
        }

        struct B<X> {
          let x: X
          public memberwise init
        }

        struct P<X, Y> {
          let x: X
          let y: Y
          public memberwise init
        }

        fun 複雑(サ a: B<Int>, シ b: P<Int, P<Bool, B<Int>>>) -> Int { Int() }
        static fun 複雑2(ス c: Int, セ: Bool) -> Bool { Bool() }

        extension <T> {Void, T} {
          fun f() {}
        }

        public fun f(x: inout Int64) auto -> Int64 {
          let   { (Int64(), ) }
          inout { Int64() }
        }

        fun g() {
          let x = Int()
          _ = x
          let f0 = fun[](a: Void) -> Void {
            let b = Int()
            _ = b
          }
        }

        """)
    await p.typeCheck(m0)

    // Exact match test cases.
    let expected: [String: (any Syntax.Type, String)] = [
      "W.X": (AssociatedTypeDeclaration.self, "M0.#.W.X"),
      "MyEnum.one": (EnumCaseDeclaration.self, "M0.#.MyEnum.one"),
      "MyEnum.two": (EnumCaseDeclaration.self, "M0.#.MyEnum.two"),
      "MyEnum": (EnumDeclaration.self, "M0.#.MyEnum"),
      "複雑(サ:シ:)": (
        FunctionDeclaration.self,
        "M0.#.fun 複雑: [Void](サ: M0.#.B<[GenericParameterUser<M0.#.B.X, *>: Hylo.Int]>, シ: M0.#.P<[GenericParameterUser<M0.#.P.X, *>: Hylo.Int], [GenericParameterUser<M0.#.P.Y, *>: M0.#.P<[GenericParameterUser<M0.#.P.X, *>: Hylo.Bool], [GenericParameterUser<M0.#.P.Y, *>: M0.#.B<[GenericParameterUser<M0.#.B.X, *>: Hylo.Int]>]>]>) let -> Hylo.Int"
      ),
      "複雑2(ス:_:)": (
        FunctionDeclaration.self,
        "M0.#.static fun 複雑2: [Void](ス: Hylo.Int, Hylo.Bool) let -> Hylo.Bool"
      ),
      "MyEnum.T": (GenericParameterDeclaration.self, "M0.#.MyEnum.T"),
      "B.X": (GenericParameterDeclaration.self, "M0.#.B.X"),
      "複雑(サ:シ:).a": (
        ParameterDeclaration.self,
        "M0.#.fun 複雑: [Void](サ: M0.#.B<[GenericParameterUser<M0.#.B.X, *>: Hylo.Int]>, シ: M0.#.P<[GenericParameterUser<M0.#.P.X, *>: Hylo.Int], [GenericParameterUser<M0.#.P.Y, *>: M0.#.P<[GenericParameterUser<M0.#.P.X, *>: Hylo.Bool], [GenericParameterUser<M0.#.P.Y, *>: M0.#.B<[GenericParameterUser<M0.#.B.X, *>: Hylo.Int]>]>]>) let -> Hylo.Int.a"
      ),
      "B": (StructDeclaration.self, "M0.#.B"),
      "P": (StructDeclaration.self, "M0.#.P"),
      // TODO (LucTeo): fix this
      // "ConformanceDeclaration.X": (
      //   TypeAliasDeclaration.self,
      //   "M0.#.given M0.#.W<[GenericParameterConformer<M0.#.W, *>: Void]> where .X"
      // ),
      "W": (TraitDeclaration.self, "M0.#.W"),
      "B.x": (VariableDeclaration.self, "M0.#.B.x"),
      "P.x": (VariableDeclaration.self, "M0.#.P.x"),
      "P.y": (VariableDeclaration.self, "M0.#.P.y"),
      "g.x": (VariableDeclaration.self, "M0.#.fun g: [Void]() let -> Void.x"),
      // TODO (LucTeo): fix this
      // "g.FunctionDeclaration.b": (
      //   VariableDeclaration.self, "M0.#.fun g: [Void]() let -> Void.$anonymous.b"
      // ),
      "f.f@let": (
        VariantDeclaration.self,
        "M0.#.fun bundle f: bundle<[Void](Hylo.Int64) auto -> Hylo.Int64, [let, inout]>.let"
      ),
      "f.f@inout": (
        VariantDeclaration.self,
        "M0.#.fun bundle f: bundle<[Void](Hylo.Int64) auto -> Hylo.Int64, [let, inout]>.inout"
      ),
    ]

    // Substring match test cases.
    let expected2: [String: (any Syntax.Type, String)] = [
      // TODO (LucTeo): fix this
      // "B.$": (BindingDeclaration.self, "M0.#.B.[x]"),
      "$<ConformanceDeclaration at": (
        ConformanceDeclaration.self,
        "M0.#.given M0.#.W<[GenericParameterConformer<M0.#.W, *>: Void]> where "
      ),
      "$<ExtensionDeclaration at": (
        ExtensionDeclaration.self,
        "M0.#.extension <GenericParameterUser<...T, *>> (Void, GenericParameterUser<...T, *>, Void) where "
      ),
    ]

    for (n, (t, r)) in expected {
      guard let d = findDeclaration(t, named: n, in: m0, of: p.base) else {
        XCTFail("unable to find declaration \(n)")
        continue
      }
      assertManglingOf(declaration: d, in: p.base, is: r)
    }
    for (n, (t, r)) in expected2 {
      guard
        let d = findDeclaration(
          t, in: m0, of: p.base,
          nameMatching: { (name) in name.contains(n) }
        )
      else {
        XCTFail("unable to find declaration with name containing \(n)")
        continue
      }
      assertManglingOf(declaration: d, in: p.base, is: r)
    }

  }

  /// Tests that the demangling for a selection of declarations don't contain errors.
  func testDeclarationsSelection() async {
    var p = await TestProgram()

    let m0 = p.addModule(
      named: "M0",
      source:
        """
        public struct A {}

        trait X {}

        trait Indexable {
          type Index
          fun index(of: Self) -> Index
          fun size() -> Index

          given Indexable is X {}
        }

        struct MyInt {
          public memberwise init
          public fun infix+ (other: Self) -> Self { Self() }
        }
        struct MyInt64 {
          public memberwise init
          public fun infix+ (other: Self) -> Self { Self() }
        }
        type Number = MyInt

        struct Angle {
          public var radians: MyInt64
          public memberwise init
          public init(degrees: MyInt64) {
            &self.radians = MyInt64()
          }
        }

        struct B<X> {
          public memberwise init
        }

        struct P<X, Y> {
          public memberwise init
        }

        fun français(_ x: MyInt, label y: A) -> MyInt {
          let (bar, ham) = (MyInt(), MyInt())
          return bar + ham
        }

        fun 複雑(サ: B<MyInt>, シ: P<MyInt, P<Bool, B<MyInt>>>) -> MyInt { MyInt() }
        fun 複雑2(ス: MyInt, セ: Bool) -> Bool { Bool() }

        fun foo(y: MyInt) {
          let local = MyInt()
          let lambda = fun[let capture = local](x x: MyInt) { capture + x }
          if Bool() {
            let z = lambda(x: y)
            _ = z
          }

          struct U {
            fun hammer() {}
          }

          given Number is X {}
        }

        fun bar() {
          let f = fun (a: Int) -> Void {}
          let g = fun (a: Int) -> Void {}
        }
        """)
    await p.typeCheck(m0)

    for d in p.base[m0].topLevelDeclarations {
      assertDemanglingIsOk(mangled: p.base.mangled(d))
    }
  }

  /// Tests demangling for declarations with more generics.
  func testDeclarationsWithMoreGenerics() async {
    var p = await TestProgram()

    let m0 = p.addModule(
      named: "M0",
      source:
        """
        trait P { type X }

        given Void is P { type X = Void }

        fun check<T>(x: T) {}

        fun f0<T where T == Void>(x: T.X) {
          check<Void>(x)
        }

        fun f1<T, U where T == U, T is P>(x: U.X) {
          check<T.X>(x)
          let y: T.X = x
        }

        fun f2<T, U where T == U, T is P, U is P, T.X == U.X>(x: U.X) {
          check<T.X>(x)
          let y: T.X = x
        }
        """)
    await p.typeCheck(m0)

    for d in p.base[m0].topLevelDeclarations {
      assertDemanglingIsOk(mangled: p.base.mangled(d))
    }
  }

  /// Tests mangling and demangling in cases where entity lookup is used internally.
  func testReuseScopes() async {
    var p = await TestProgram()

    let m0 = p.addModule(
      named: "M0",
      source:
        """
        struct A {
          public memberwise init

          struct X {}
          struct Y {}
        }
        struct B {
          public memberwise init

          struct X {}
          struct Y {}

          fun f1(x: X, y: Y) {}
          fun f2(x: A.X, y: A.Y) {}
        }

        """)
    await p.typeCheck(m0)

    let expected: [String: (any Syntax.Type, String)] = [
      "A.X": (StructDeclaration.self, "M0.#.A.X"),
      "A.Y": (StructDeclaration.self, "M0.#.A.Y"),
      "B.X": (StructDeclaration.self, "M0.#.B.X"),
      "B.Y": (StructDeclaration.self, "M0.#.B.Y"),
      "B.f1(_:_:)": (
        FunctionDeclaration.self,
        "M0.#.B.fun f1: [Void](self: M0.#.B, M0.#.B.X, M0.#.B.Y) let -> Void"
      ),
      "B.f2(_:_:)": (
        FunctionDeclaration.self,
        "M0.#.B.fun f2: [Void](self: M0.#.B, M0.#.A.X, M0.#.A.Y) let -> Void"
      ),
    ]

    for (n, (t, r)) in expected {
      guard let d = findDeclaration(t, named: n, in: m0, of: p.base) else {
        XCTFail("unable to find declaration \(n)")
        continue
      }
      assertManglingOf(declaration: d, in: p.base, is: r)
    }
  }

  /// Tests the mangling and demangling of reserved types in `program`.
  private func testReservedTypesMangling(program: inout Program) {
    let never = AnyTypeIdentity(program.types.never())
    assertManglingOf(type: never, in: program, is: "Never")
    assertManglingOf(type: .void, in: program, is: "Void")
  }

  /// Tests the mangling and demangling of core types in `program`.
  private func testCoreTypesMangling(program: inout Program) {
    assertManglingOf(type: program.standardLibraryType(.bool), in: program, is: "Hylo.Bool")
    assertManglingOf(type: program.standardLibraryType(.int), in: program, is: "Hylo.Int")
    assertManglingOf(type: program.standardLibraryType(.int64), in: program, is: "Hylo.Int64")
  }

  /// Tests the mangling and demangling of arrow types in `program`.
  private func testArrowTypeMangling(program: inout Program) {
    let int = program.standardLibraryType(.int)
    let int64 = program.standardLibraryType(.int64)
    let bool = program.standardLibraryType(.bool)

    let arrow = Arrow(
      effect: .inout,
      environment: int64,
      inputs: [
        .init(label: "x", access: .let, type: int),
        .init(label: "y", access: .sink, type: int64),
      ],
      output: bool)

    assertManglingOf(
      type: program.types.demand(arrow).erased, in: program,
      is: "[Hylo.Int64](x: Hylo.Int, y: Hylo.Int64) inout -> Hylo.Bool")
  }

  /// Tests the mangling and demangling of associated types in `program`.
  private func testAssociatedTypeMangling(module m: Module.ID, program: inout Program) {
    let provider = findTopLevelDeclaration(named: "Provider", in: m, of: program)!
    let traitDeclaration = TraitDeclaration.ID(uncheckedFrom: provider.erased)
    let providerRequirement = program.types.demand(Trait(declaration: traitDeclaration))
    let providerType = providerRequirement.erased
    let providerSelf = program.types.demand(GenericParameter.conformer(traitDeclaration, .proper))
    let providerWitness = WitnessExpression(
      value: .abstract,
      type: program.types.demand(
        TypeApplication(abstraction: providerType, arguments: [providerSelf: providerSelf.erased])
      ).erased)
    let output = program.requirements(of: providerRequirement).associatedTypes.first!

    assertManglingOf(
      type: program.types.demand(
        AssociatedType(
          declaration: output,
          qualification: providerWitness
        )
      ).erased, in: program,
      is:
        "M0.#.Provider.Output.M0.#.Provider<[GenericParameterConformer<M0.#.Provider, *>: GenericParameterConformer<M0.#.Provider, *>]>"
    )
  }

  /// Tests the mangling and demangling of enum types in `program`.
  private func testEnumTypeMangling(module m: Module.ID, program: inout Program) {
    let d = findTopLevelDeclaration(named: "MyEnum", in: m, of: program)!
    assertManglingOf(
      type: program.types.demand(
        Enum(declaration: .init(uncheckedFrom: d.erased))
      ).erased, in: program,
      is: "M0.#.MyEnum")
  }

  /// Tests the mangling and demangling of equality witness types in `program`.
  private func testEqualityWitnessMangling(program: inout Program) {
    let int = program.standardLibraryType(.int)
    let int64 = program.standardLibraryType(.int64)
    let t = EqualityWitness(lhs: int.erased, rhs: int64.erased)
    assertManglingOf(
      type: program.types.demand(t).erased, in: program, is: "Hylo.Int == Hylo.Int64")
  }

  /// Tests the mangling and demangling of function pointer types in `program`.
  private func testFunctionPointerMangling(program: inout Program) {
    let int = program.standardLibraryType(.int)
    let int64 = program.standardLibraryType(.int64)
    let bool = program.standardLibraryType(.bool)
    let arrow = program.types.demand(
      Arrow(
        effect: .inout,
        environment: int64,
        inputs: [
          .init(label: "x", access: .set, type: int),
          .init(label: "y", access: .inout, type: int64),
        ],
        output: bool))
    let t = program.types.pointer(to: arrow).erased
    assertManglingOf(
      type: t, in: program, is: "ptr (Hylo.Int64, Hylo.Int, Hylo.Int64) -> Hylo.Bool")
  }

  /// Tests the mangling and demangling of generic parameter types in `program`.
  private func testGenericParameterMangling(module m: Module.ID, program: inout Program) {
    let provider = Array(program.collectTopLevel(TraitDeclaration.self, of: m)).first!
    assertManglingOf(
      type: program.types.demand(GenericParameter.conformer(provider, .proper)).erased,
      in: program,
      is: "GenericParameterConformer<M0.#.Provider, *>")

    let myEnum = Array(program.collectTopLevel(EnumDeclaration.self, of: m)).first!
    let userParameter = program[myEnum].parameters.first!
    assertManglingOf(
      type: program.types.demand(GenericParameter.user(userParameter, .proper)).erased,
      in: program,
      is: "GenericParameterUser<M0.#.MyEnum.T, *>")

    assertManglingOf(
      type: program.types.demand(GenericParameter.nth(3, .proper)).erased,
      in: program,
      is: "GenericParameterNth<3, *>")
  }

  /// Tests the mangling and demangling of implication types in `program`.
  private func testImplicationTypeMangling(program: inout Program) {
    let bool = program.standardLibraryType(.bool)
    let int = program.standardLibraryType(.int)
    let int64 = program.standardLibraryType(.int64)
    let t = Implication(context: [bool.erased, int.erased], head: int64.erased)
    assertManglingOf(
      type: program.types.demand(t).erased, in: program, is: "(Hylo.Bool, Hylo.Int) => Hylo.Int64")
  }

  /// Tests the mangling and demangling of literal types in `program`.
  private func testLiteralTypeMangling(program: inout Program) {
    assertManglingOf(
      type: program.types.demand(LiteralType.integer).erased,
      in: program,
      is: "IntegerLiteral")
    assertManglingOf(
      type: program.types.demand(LiteralType.float).erased,
      in: program,
      is: "FloatLiteral")
  }

  /// Tests the mangling and demangling of machine types in `program`.
  private func testMachineTypeMangling(program: inout Program) {
    let expected: [(MachineType, String)] = [
      (MachineType.i(8), "i8"),
      (MachineType.i(16), "i16"),
      (MachineType.i(32), "i32"),
      (MachineType.i(64), "i64"),
      (MachineType.word, "word"),
      (MachineType.float16, "float16"),
      (MachineType.float32, "float32"),
      (MachineType.float64, "float64"),
      (MachineType.float128, "float128"),
      (MachineType.ptr, "ptr"),
    ]

    for (type, mangling) in expected {
      assertManglingOf(type: program.types.demand(type).erased, in: program, is: mangling)
    }
  }

  /// Tests the mangling and demangling of metakind types in `program`.
  private func testMetakindTypeMangling(program: inout Program) {
    assertManglingOf(
      type: program.types.demand(Metakind(inhabitant: .proper)).erased,
      in: program,
      is: "Metakind<*>")
  }

  /// Tests the mangling and demangling of opaque environment types in `program`.
  private func testOpaqueEnvironmentTypeMangling(module m: Module.ID, program: inout Program) {
    let d = findTopLevelDeclaration(named: "MyEnum", in: m, of: program)!
    let t = OpaqueType.environment(d)
    assertManglingOf(type: program.types.demand(t).erased, in: program, is: "some M0.#.MyEnum")
  }

  /// Tests the mangling and demangling of remote types in `program`.
  private func testRemoteTypeMangling(program: inout Program) {
    let int = program.standardLibraryType(.int)
    let t = RemoteType(projectee: int.erased, access: .inout)
    assertManglingOf(type: program.types.demand(t).erased, in: program, is: "inout Hylo.Int")
  }

  /// Tests the mangling and demangling of struct types in `program`.
  private func testStructTypeMangling(module m: Module.ID, program: inout Program) {
    let d = findTopLevelDeclaration(named: "A", in: m, of: program)!
    let t = Struct(declaration: .init(uncheckedFrom: d.erased))
    assertManglingOf(type: program.types.demand(t).erased, in: program, is: "M0.#.A")
  }

  /// Tests the mangling and demangling of trait types in `program`.
  private func testTraitTypeMangling(module m: Module.ID, program: inout Program) {
    let d = findTopLevelDeclaration(named: "Provider", in: m, of: program)!
    let t = Trait(declaration: .init(uncheckedFrom: d.erased))
    assertManglingOf(type: program.types.demand(t).erased, in: program, is: "M0.#.Provider")
  }

  /// Tests the mangling and demangling of tuple types in `program`.
  private func testTupleTypeMangling(program: inout Program) {
    let bool = program.standardLibraryType(.bool)
    let int = program.standardLibraryType(.int)
    let t2 = Tuple.cons(head: bool.erased, tail: .void)
    assertManglingOf(type: program.types.demand(t2).erased, in: program, is: "(Hylo.Bool, Void)")

    let t3 = Tuple.cons(
      head: bool.erased,
      tail: program.types.demand(Tuple.cons(head: int.erased, tail: .void)).erased)
    assertManglingOf(
      type: program.types.demand(t3).erased, in: program, is: "(Hylo.Bool, Hylo.Int, Void)")
  }

  /// Tests the mangling and demangling of type application types in `program`.
  private func testTypeApplicationMangling(module m: Module.ID, program: inout Program) {
    let int = program.standardLibraryType(.int)
    let myEnum = Array(program.collectTopLevel(EnumDeclaration.self, of: m)).first!
    let enumParameter = program[myEnum].parameters.first!
    let formal = program.types.demand(GenericParameter.user(enumParameter, .proper))
    let abstraction = program.types.demand(Enum(declaration: myEnum)).erased
    let t = TypeApplication(abstraction: abstraction, arguments: [formal: int.erased])
    assertManglingOf(
      type: program.types.demand(t).erased,
      in: program,
      is: "M0.#.MyEnum<[GenericParameterUser<M0.#.MyEnum.T, *>: Hylo.Int]>")
  }

  /// Tests the mangling and demangling of universal types in `program`.
  private func testUniversalTypeMangling(program: inout Program) {
    let parameter = program.types.demand(GenericParameter.nth(1, .proper))
    let t = UniversalType(parameters: [parameter], head: parameter.erased)
    assertManglingOf(
      type: program.types.demand(t).erased,
      in: program,
      is: "<GenericParameterNth<1, *>> GenericParameterNth<1, *>")
  }

  /// Tests the mangling and demangling of type alias types in `program`.
  private func testTypeAliasMangling(module m: Module.ID, program: inout Program) {
    let c = findTopLevelDeclaration(named: "C", in: m, of: program)!
    let output = (program[c] as! StructDeclaration).members[0]
    assertManglingOf(
      type: program.type(assignedTo: output),
      in: program,
      is: "Metatype<typealias M0.#.C.Output = Hylo.Int>")
  }

  /// Asserts that the mangling of `t` in `p` equals `expected`.
  private func assertManglingOf(type t: AnyTypeIdentity, in p: Program, is expected: String) {
    let m = p.mangled(t)
    let demangled = DemangledSymbol(m).description
    XCTAssertEqual(
      demangled, expected,
      "demangling of type \(t) is incorrect (mangled: \(m))"
    )
  }

  /// Asserts that the mangling of `d` in `p` equals `expected`.
  private func assertManglingOf(
    declaration d: DeclarationIdentity, in p: Program, is expected: String
  ) {
    let m = p.mangled(d)
    let demangled = DemangledSymbol(m).description
    XCTAssertEqual(
      demangled, expected,
      "demangling of declaration \(d) is incorrect (mangled: \(m))"
    )
  }

  /// Asserts that the mangling of `t` in `p` equals `expected`.
  private func assertDemanglingIsOk(mangled m: String) {
    let demangled = DemangledSymbol(m).description
    XCTAssertFalse(demangled.contains("?"), "demangling of \(m) contains errors: \(demangled)")
  }

  /// Finds the first top-level declaration of `m` named `n`, returning its identity, or `nil` if
  /// no such declaration exists.
  private func findTopLevelDeclaration(
    named n: String, in m: Module.ID, of program: Program
  ) -> DeclarationIdentity? {
    program[m].topLevelDeclarations.first { d in
      return program.debugName(of: d) == n
    }
  }

  /// Finds the first declaration of `m` of type `t`, named `n`, returning its identity, or
  /// `nil` if no such declaration exists.
  private func findDeclaration<T: Syntax>(
    _ t: T.Type, named n: String, in m: Module.ID, of program: Program
  ) -> DeclarationIdentity? {
    findDeclaration(t, in: m, of: program) { $0 == n }
  }

  /// Finds the first declaration of `m` of type `t`, that has a name for which `predicate` returns
  /// `true`, returning its identity, or `nil` if no such declaration exists.
  private func findDeclaration<T: Syntax>(
    _ t: T.Type, in m: Module.ID, of program: Program, nameMatching predicate: (String) -> Bool
  ) -> DeclarationIdentity? {
    let u = SyntaxTag(t)
    for s in program[m].syntax {
      if program.tag(of: s) == u && program.isDeclaration(s) {
        let d = DeclarationIdentity(uncheckedFrom: s)
        if predicate(program.debugName(of: d)) {
          return d
        }
      }
    }
    return nil
  }

  /// A test program with a minimal standard library.
  struct TestProgram {

    /// The base program.
    var base: Program

    /// The identity of the standard library module in `base`.
    let standardLibraryModule: Module.ID

    /// An instance with a minimal standard library, ready for testing.
    init() async {
      self.base = .init()
      base.allowPartialStandardLibrary = true
      self.standardLibraryModule = base.demandModule(Module.standardLibraryName)
      _ = base[standardLibraryModule].addSource(
        """
        @_symbol("Bool")
        public struct Bool {

          public memberwise init

        }

        @_symbol("Int")
        public struct Int {

          public memberwise init

        }

        @_symbol("Int64")
        public struct Int64 {

          public memberwise init

        }
        """)
      await typeCheck(standardLibraryModule)
    }

    /// Adds a new module named `name` with source `source` to `base`, making it depend on the
    /// standard library, and returns its identity.
    mutating func addModule(named name: String, source: SourceFile) -> Module.ID {
      let m = base.demandModule(Module.Name(name))
      _ = base[m].addSource(source)
      base[m].addDependency(Module.standardLibraryName)
      return m
    }

    /// Type checks `m`, failing the tests if that contains an error.
    mutating func typeCheck(_ m: Module.ID) async {
      await base.assignScopes(m)
      failIfContainsError(m)
      base.assignTypes(m, loggingInferenceWhere: nil)
      failIfContainsError(m)
    }

    /// Fail the tests if `m` contains errors.
    private func failIfContainsError(_ m: Module.ID) {
      if base[m].containsError {
        for d in base[m].diagnostics {
          print(d)
        }
        XCTFail("Unexpected error(s) in module \(base[m].name): \(base[m].diagnostics)")
      }
    }

  }

}

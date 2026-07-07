import FrontEnd
import XCTest

/// Tests for `Program.declarations(visibleFrom:in:)`, the unqualified-visibility query used by
/// LSP completion.
///
/// The query delegates shadowing and overload collection to `Typer.lookup(_:unqualifiedIn:)`, so
/// these tests pin the visible set — including what lookup's shadowing must exclude — for each
/// tier of the walk: lexical scopes, the module's other source files, and imports.
final class VisibleDeclarationsTests: XCTestCase {

  func testFileScopeSeesEveryFileOfTheModule() async throws {
    // The walk starts at the file's own top level and continues with the top level of the
    // module's other source files.
    var p = Program()
    let m = p.demandModule(.init("Main"))
    let (_, f) = p[m].addSource("public fun one() {}")
    _ = p[m].addSource("public struct Two { public memberwise init }")
    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: nil)

    let names = names(of: p.declarations(visibleFrom: .init(file: f), in: m), in: p)
    XCTAssert(names.contains("one"))  // this file
    XCTAssert(names.contains("Two"))  // other file
  }

  func testSameScopeOverloadsAreAllReturned() async throws {
    // Declarations sharing a name in one scope are overloads; none may be dropped.
    var p = Program()
    let (m, f) = await typeChecked(
      &p,
      """
      fun a() {}
      fun a(x: Int) {}
      struct Int { public memberwise init }
      """)

    let ds = p.declarations(visibleFrom: .init(file: f), in: m)
    XCTAssertEqual(ds.count(where: { (d) in p.name(of: d)?.identifier == "a" }), 2)
  }

  func testInnerBindingShadowsOuterFunction() async throws {
    // A binding is not overloadable: it hides a same-named declaration of any outer scope.
    var p = Program()
    let (m, _) = await typeChecked(
      &p,
      """
      fun value() {}

      public fun main() {
        let value = value
        fun probe() {}
      }
      """)

    let ds = try declarations(visibleFromFunctionNamed: "probe", in: &p, module: m)
    let matches = ds.filter { (d) in p.name(of: d)?.identifier == "value" }
    XCTAssertEqual(matches.count, 1)
    XCTAssertEqual(matches.first.map { (d) in p.tag(of: d) }, .init(VariableDeclaration.self))
  }

  func testShadowedBindingStillEndsItsNameLookup() async throws {
    // `Typer.lookup` stops a name's walk at the first scope containing a non-overloadable
    // declaration even when an inner overloadable match already won: the middle `let f` is not
    // itself returned, but it still makes the outermost `f` unreachable.
    var p = Program()
    let (m, _) = await typeChecked(
      &p,
      """
      fun f(x: Int) {}

      public fun main() {
        let f = ()
        fun g() {
          fun f() {}
          fun probe() {}
        }
        g()
      }
      struct Int { public memberwise init }
      """)

    let ds = try declarations(visibleFromFunctionNamed: "probe", in: &p, module: m)
    let matches = ds.filter { (d) in p.name(of: d)?.identifier == "f" }
    XCTAssertEqual(matches.count, 1)
    let survivor = try XCTUnwrap(matches.first)
    XCTAssertEqual(p.tag(of: survivor), .init(FunctionDeclaration.self))
    XCTAssert(p.isLocal(survivor), "the surviving `f` is the innermost one")
  }

  func testMemberFunctionScopeSeesMembersAndTopLevel() async throws {
    // The lexical walk passes through the type's scope: members (stored properties, methods,
    // static functions) are visible from a method body, along with the file's top level.
    var p = Program()
    let (m, _) = await typeChecked(
      &p,
      """
      struct A {
        public memberwise init
        var x: Int
        public fun m() {
          fun probe() {}
        }
        public static fun s() {}
      }
      fun free() {}
      struct Int { public memberwise init }
      """)

    let ds = try declarations(visibleFromFunctionNamed: "probe", in: &p, module: m)
    let names = names(of: ds, in: p)
    XCTAssert(names.isSuperset(of: ["x", "m", "s", "free", "A"]))
    XCTAssertEqual(Set(ds).count, ds.count, "no declaration is returned twice")
  }

  func testImportedModuleTopLevelIsVisible() async throws {
    // The walk ends with the imports of the file, which include the standard library implicitly.
    var p = await Program.withMinimalStandardLibrary()
    let m = p.addUserModule(named: "Main", source: "public fun main() {}")

    p = await p.typeChecked()

    let f = try XCTUnwrap(p[m].sourceFileIdentities.first)
    let names = names(of: p.declarations(visibleFrom: .init(file: f), in: m), in: p)
    XCTAssert(names.isSuperset(of: ["Int", "Bool", "main"]))
  }

  // MARK: - Helpers

  /// Returns the identifiers of `ds` in `p`.
  private func names(of ds: [DeclarationIdentity], in p: Program) -> Set<String> {
    Set(ds.compactMap { (d) in p.name(of: d)?.identifier })
  }

  /// Returns the declarations visible from the scope of the function declaration named `n`.
  private func declarations(
    visibleFromFunctionNamed n: String, in p: inout Program, module m: Module.ID,
    file: StaticString = #filePath, line: UInt = #line
  ) throws -> [DeclarationIdentity] {
    let d = try XCTUnwrap(
      p.select(.and(.tag(FunctionDeclaration.self), .name(.init(identifier: n)))).first,
      "no function named '\(n)'", file: file, line: line)
    return p.declarations(visibleFrom: .init(uncheckedFrom: d.erased), in: m)
  }

  /// Type-checks `source` as a single-file `Main` module in `p`, returning its module and file.
  private func typeChecked(
    _ p: inout Program, _ source: SourceFile
  ) async -> (module: Module.ID, file: SourceFile.ID) {
    let m = p.demandModule(.init("Main"))
    let (_, f) = p[m].addSource(source)
    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: nil)
    return (m, f)
  }

}

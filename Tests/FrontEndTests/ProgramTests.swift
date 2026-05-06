import Archivist
import Foundation
import FrontEnd
import XCTest

final class ProgramTests: XCTestCase {

  func testSelectAll() throws {
    let p = Program.test
    XCTAssertEqual(p.select(.all).count, 8)
  }

  func testSelectByModule() throws {
    let p = Program.test
    let m = p.identity(module: .init("M0"))!
    XCTAssertEqual(p.select(from: m, .all).count, 4)
  }

  func testSelectByTag() throws {
    let p = Program.test
    XCTAssertEqual(p.select(.tag(AssociatedTypeDeclaration.self)).count, 4)
  }

  func testFormat() throws {
    let p = Program.test
    let v = AnyTypeIdentity.void
    XCTAssertEqual(p.format("> xy <", []), "> xy <")
    XCTAssertEqual(p.format("> %S, %S <", [10, true]), "> 10, true <")
    XCTAssertEqual(p.format("> %T <", [v]), "> Void <")
    XCTAssertEqual(p.format("> %T* <", [[v, v]]), "> Void, Void <")
    XCTAssertEqual(p.format("> %% <", [v]), "> % <")
  }

  func testArchiveConsistency() throws {
    let p = Program.test
    let m = p.moduleIdentities.first!

    var w1 = WriteableArchive(BinaryBuffer())
    try p.write(module: m, to: &w1)
    var w2 = WriteableArchive(BinaryBuffer())
    try p.write(module: m, to: &w2)
    XCTAssertEqual(w1.finalize(), w2.finalize())
  }

  func testSerializationRoundTrip() throws {
    let p = Program.test
    let m = p.moduleIdentities.first!
    let a = try p.archive(module: m)

    var q = Program()
    let (loaded, n) = try q.load(module: p[m].name, from: a)

    // Syntax trees should have the same identities.
    XCTAssert(loaded)
    XCTAssertEqual(p[m].name, q[n].name)
    for (l, r) in zip(p.select(from: m, .all), q.select(from: n, .all)) {
      assertIsomorphic(l, r)
    }

    /// Asserts that `l` and `r`, which are in `p` and `q` respectively, are equal up to renaming
    /// of tree identities.
    func assertIsomorphic(_ l: AnySyntaxIdentity, _ r: AnySyntaxIdentity) {
      XCTAssert(p[l].equals(q[r]))
    }
  }

  func testSerializationWithDependencies() throws {
    let p = Program.test

    var archives: [(identity: Module.ID, data: BinaryBuffer)] = []
    for m in p.moduleIdentities {
      try archives.append((m, p.archive(module: m)))
    }

    var q = Program()

    // Re-load modules out of order.
    var loaded = false
    (loaded, _) = try q.load(module: p[archives[0].identity].name, from: archives[0].data)
    XCTAssert(loaded)
    (loaded, _) = try q.load(module: p[archives[2].identity].name, from: archives[2].data)
    XCTAssert(loaded)
    (loaded, _) = try q.load(module: p[archives[1].identity].name, from: archives[1].data)
    XCTAssert(loaded)
  }

  func testGivensCanBeQueriedThroughTypeCheckedProgram() async throws {
    var p = Program()
    let m = p.demandModule(.init("Main"))
    let (_, f) = p[m].addSource(
      """
      trait P {}

      struct A { 
        given w1: B is P {}
      }

      struct B {}

      given w2: A is P {}
      """)

    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: nil)

    // Query givens visible from the file level.
    let givens = p.givens(in: m, visibleFrom: .init(file: f))

    // The visible given should be the top-level `w2`.
    guard givens.count == 1, case .user(let given) = givens[0] else {
      return XCTFail("expected exactly one user-defined given, got \(givens)")
    }

    let w2 = try XCTUnwrap(
      p.select(from: m, .and(.tag(ConformanceDeclaration.self), .name(.init(identifier: "w2"))))
        .first)
    XCTAssertEqual(given.erased, w2)
  }

  func testQueryingSourceFileWithName() throws {
    var p = Program()

    let m0 = p.demandModule("M0")
    let s0: SourceFile = "trait A {}"
    let (_, id0) = p[m0].addSource(s0)

    let m1 = p.demandModule("M1")
    let s1: SourceFile = "trait B {}"
    let (_, id1) = p[m1].addSource(s1)

    // Sources that are present should be found:
    let f0 = try XCTUnwrap(p.sourceFile(named: s0.name))
    XCTAssertEqual(f0, id0)
    XCTAssertEqual(p[sourceFile: f0], s0)

    let f1 = try XCTUnwrap(p.sourceFile(named: s1.name))
    XCTAssertEqual(f1, id1)
    XCTAssertEqual(p[sourceFile: f1], s1)

    // Missing sources should result in nil:
    let missing: FileName = .virtual(URL(string: "virtual:///nonexistent")!)
    XCTAssertNil(p.sourceFile(named: missing))
  }

  func testQueryingSourceFileLevelDiagnostics() throws {
    var p = Program()
    let m = p.demandModule("Main")
    let s0: SourceFile = "trait Foo {}"
    let s1: SourceFile = "trait Bar {}"
    let (_, id0) = p[m].addSource(s0)
    let (_, id1) = p[m].addSource(s1)

    // Well-formed sources have no diagnostics.
    XCTAssert(p.diagnostics(in: id0).elements.isEmpty)
    XCTAssert(p.diagnostics(in: id1).elements.isEmpty)

    // Adding a diagnostic to one source file must not affect the other.
    p[m].addDiagnostic(.init(.error, "boom", at: p[sourceFile: id0].span))

    let ds0 = p.diagnostics(in: id0)
    XCTAssertEqual(ds0.elements.count, 1)
    XCTAssert(ds0.containsError)

    let ds1 = p.diagnostics(in: id1)
    XCTAssert(ds1.elements.isEmpty)
    XCTAssertFalse(ds1.containsError)
  }

  func testQueryingTopLevelDeclarationsPerSourceFile() async throws {
    var p = Program()
    let m = p.demandModule("Main")
    let (_, id) = p[m].addSource(
      """
      trait A {}
      struct B {}
      """)

    _ = p[m].addSource(
      """
      enum C {}
      """)

    await p.assignScopes(m)

    let ds = Array(p.topLevelDeclarations(in: id))

    // `ds` should contain exactly the declarations from the first source file, and not
    // ones from the second.
    XCTAssertEqual(ds.count, 2)

    let tags = Set(ds.map { p.tag(of: $0) })
    XCTAssert(tags.contains(.init(TraitDeclaration.self)))
    XCTAssert(tags.contains(.init(StructDeclaration.self)))
    XCTAssertFalse(tags.contains(.init(EnumDeclaration.self)))
  }

  func testReturnsNilDeclarationIffNameIsNotResolved() async throws {
    var p = Program()
    let m = p.demandModule("Main")
    let s: SourceFile = """
      let x = nonexistent.y
      let z = x
      """
    _ = p[m].addSource(s)

    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: { _, _ in false })

    func isVariable(referringTo name: String) -> (AnySyntaxIdentity) -> Bool {
      { (n: AnySyntaxIdentity) -> Bool in
        if let n = p.cast(n, to: NameExpression.self),
          p[n].name.value.identifier == name
        {
          return true
        }
        return false
      }
    }

    // y should not refer to anything
    let y = try XCTUnwrap(p.select(.satisfies(isVariable(referringTo: "y"))).first)
    guard let yn = p.cast(y, to: NameExpression.self) else {
      return XCTFail("y is not a name expression")
    }
    XCTAssertEqual(p.declaration(ifReferredToBy: yn), nil)

    // x usage should refer to `x` declaration
    let x = try XCTUnwrap(p.select(.satisfies(isVariable(referringTo: "x"))).first)
    guard let xName = p.cast(x, to: NameExpression.self) else {
      return XCTFail("x is not a name expression")
    }
    let xd = try XCTUnwrap(p.select(.name("x")).first).erased
    XCTAssertEqual(p.declaration(ifReferredToBy: xName)?.target?.erased, xd)
  }

  func testReturnsNilTypeIfCouldntTypeCheck() async throws {
    let s: SourceFile = """
      let (e, b) = ((), (), ())
      """
    var p = Program()
    let m = p.demandModule("Main")
    _ = p[m].addSource(s)
    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: { _, _ in false })
    
    // `e` should not have a type; it's not assigned.
    let e = try XCTUnwrap(p.select(.name("e")).first)
    XCTAssertNil(p.type(ifAssignedTo: e))
  }

}

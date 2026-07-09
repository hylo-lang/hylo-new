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

    var q = Program(forTesting: true)
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

    var q = Program(forTesting: true)

    // Re-load modules out of order.
    var loaded = false
    (loaded, _) = try q.load(module: p[archives[0].identity].name, from: archives[0].data)
    XCTAssert(loaded)
    (loaded, _) = try q.load(module: p[archives[2].identity].name, from: archives[2].data)
    XCTAssert(loaded)
    (loaded, _) = try q.load(module: p[archives[1].identity].name, from: archives[1].data)
    XCTAssert(loaded)
  }

  func testSerializationWithIR() async throws {
    var p = try await Program.withStandardLibrary()
    let m = p.identity(module: Module.standardLibraryName)!

    // Compile the standard library to IR and archive it.
    p.lower(m)
    p.applyTransformationPasses(m)
    let a = try p.archive(module: m)

    // Reload the standard library from the archive.
    var q = Program(forTesting: true)
    let (loaded, n) = try q.load(module: p[m].name, from: a)
    XCTAssert(loaded)

    // Check that all functions have been deserialized.
    XCTAssertEqual(p[m].ir.functions.count, q[n].ir.functions.count)
    for (f, g) in zip(p[m].ir.functions.values, q[n].ir.functions.values) {
      XCTAssert(f.blocks.count == g.blocks.count)
      XCTAssert(f.instructions().count == g.instructions().count)
    }
  }

  func testQueryGivenFromCheckedProgram() async throws {
    var (p, m, s) = try await Program.typeCheckedForTesting(
      """
      trait P {}
      struct A { given w1: B is P {} }
      struct B {}
      given w2: A is P {}
      """)

    // Query givens visible from the top-level scope of the file.
    let givens = p.givens(in: m, visibleFrom: .init(file: s))

    // The visible given should be the top-level `w2`.
    if case .user(let g) = givens.uniqueElement {
      let w2 = try XCTUnwrap(
        p.select(
          from: m,
          .and(.tag(ConformanceDeclaration.self), .name(.init(identifier: "w2")))).first)
      XCTAssertEqual(g.erased, w2)
    } else {
      XCTFail("expected exactly one user-defined given, found \(givens.count)")
    }
  }

  func testQuerySourceFileWithName() throws {
    var p = Program(forTesting: true)

    let m0 = p.demandModule("M0")
    let s0: SourceFile = "trait A {}"
    let (_, i0) = p[m0].addSource(s0)

    let m1 = p.demandModule("M1")
    let s1: SourceFile = "trait B {}"
    let (_, i1) = p[m1].addSource(s1)

    // Sources that are present should be found:
    let f0 = try XCTUnwrap(p.sourceFile(named: s0.name))
    XCTAssertEqual(f0, i0)
    XCTAssertEqual(p[sourceFile: f0], s0)

    let f1 = try XCTUnwrap(p.sourceFile(named: s1.name))
    XCTAssertEqual(f1, i1)
    XCTAssertEqual(p[sourceFile: f1], s1)

    // Missing sources should result in nil.
    let missing: FileName = .virtual(URL(string: "virtual:///nonexistent")!)
    XCTAssertNil(p.sourceFile(named: missing))
  }

  func testQuerySourceFileLevelDiagnostics() throws {
    var p = Program(forTesting: true)
    let m = p.demandModule("Main")
    let (_, s0) = p[m].addSource("trait Foo {}")
    let (_, s1) = p[m].addSource("trait Bar {}")

    // Well-formed sources have no diagnostics.
    XCTAssert(p.diagnostics(in: s0).elements.isEmpty)
    XCTAssert(p.diagnostics(in: s1).elements.isEmpty)

    // Adding a diagnostic to one source file must not affect the other.
    p[m].addDiagnostic(.init(.error, "boom", at: p[sourceFile: s0].span))

    let d0 = p.diagnostics(in: s0)
    XCTAssertEqual(d0.elements.count, 1)
    XCTAssert(d0.containsError)

    let d1 = p.diagnostics(in: s1)
    XCTAssert(d1.elements.isEmpty)
    XCTAssertFalse(d1.containsError)
  }

  func testQueryTopLevelDeclarationsPerSourceFile() async throws {
    var p = Program(forTesting: true)
    let m = p.demandModule("Main")
    let (_, s) = p[m].addSource("trait A {} ; struct B {}")
    _ = p[m].addSource("enum C {}")

    await p.assignScopes(m)

    // `ds` should contain the declarations from the first source  only.
    let ds = Array(p.topLevelDeclarations(in: s))
    XCTAssertEqual(ds.count, 2)

    let tags = Set(ds.map(p.tag(of:)))
    XCTAssert(tags.contains(.init(TraitDeclaration.self)))
    XCTAssert(tags.contains(.init(StructDeclaration.self)))
    XCTAssertFalse(tags.contains(.init(EnumDeclaration.self)))
  }

  func testDeclarationMaybeReferredToByNil() async throws {
    let (p, _, _) = try await Program.typeCheckedForTesting(
      "let x = nonexistent.y ; let z = x", assertingNoDiagnostics: false)

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
    XCTAssertEqual(p.declaration(maybeReferredToBy: yn), nil)

    // x usage should refer to `x` declaration
    let x = try XCTUnwrap(p.select(.satisfies(isVariable(referringTo: "x"))).first)
    guard let xName = p.cast(x, to: NameExpression.self) else {
      return XCTFail("x is not a name expression")
    }
    let xd = try XCTUnwrap(p.select(.name("x")).first).erased
    XCTAssertEqual(p.declaration(maybeReferredToBy: xName)?.target?.erased, xd)
  }

  func testTypeMaybeAssignedNil() async throws {
    let (p, _, _) = try await Program.typeCheckedForTesting(
      "let (ill, typed) = ((), (), ())",
      assertingNoDiagnostics: false)

    // `ill` should not have a type; it's not assigned.
    let e = try XCTUnwrap(p.select(.name("ill")).first)
    XCTAssertNil(p.type(maybeAssignedTo: e))
  }

  func testTypeOfSelfIsTheEnclosingTypeWithinAStructScope() async throws {
    // "Self" inside a struct's body denotes an instance of that struct.
    var (p, _, _) = try await Program.typeCheckedForTesting(
      """
      struct A {
        public memberwise init
      }
      """)

    let d = try XCTUnwrap(
      p.select(.and(
        .tag(StructDeclaration.self),
        .name(.init(identifier: "A")))).first, "no struct named 'A'")

    // The type of `Self` should be spelled as the underlying type.
    let t = try XCTUnwrap(p.typeOfSelf(in: .init(uncheckedFrom: d.erased)))
    XCTAssertEqual(p.show(t), "A")
  }

  func testTypeOfSelfIsNilAtFileScope() async throws {
    // "Self" is not legal at the top level of a file, where no type encloses the use.
    var (p, _, s ) = try await Program.typeCheckedForTesting(
      """
      struct A {
        public memberwise init
      }
      """)

    XCTAssertNil(p.typeOfSelf(in: .init(file: s)))
  }

}

extension Program {

  /// Creates a program from a single source file `s`, returning the program, the fixture's module 
  /// and source file identity.
  ///
  /// Throws if `assertNoDiagnostics` is true and the program contains an error.
  static func typeCheckedForTesting(
    _ s: SourceFile, assertingNoDiagnostics: Bool = true
  ) async throws -> (Program, Module.ID, SourceFile.ID) {
    var p = Program(forTesting: true)
    let m = p.demandModule("Main")
    let s = p[m].addSource(s).identity

    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: { _, _ in false })

    if assertingNoDiagnostics && p.containsError {
      throw CompilationError(DiagnosticSet(p.diagnostics))
    }
    return (p, m, s)
  }

}

/// An error that occurred during compilation.
struct CompilationError: Error {
  let diagnostics: DiagnosticSet

  /// The diagnostics of the error.
  init(_ diagnostics: DiagnosticSet) {
    self.diagnostics = diagnostics
  }
}

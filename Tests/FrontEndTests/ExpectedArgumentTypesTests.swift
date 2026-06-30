import FrontEnd
import XCTest

/// Tests for `Program.expectedArgumentTypes(at:ofCall:in:visibleFrom:)`, the overload-viability
/// query behind leading-dot completion in call arguments (`f(.<cursor>)`).
///
/// Each fixture puts the unresolvable identifier `hole` in the completed position, mirroring the
/// LSP's sentinel: the call fails to type-check, which is the state completion always queries.
/// Note that a failing call may still be partially elaborated — the checker can materialize
/// defaulted arguments (unlabeled) into the argument list and, when the callee has a single
/// candidate, rewrite it into a `SyntheticExpression` — so the query must cope with both the
/// written and the elaborated shape of a call.
final class ExpectedArgumentTypesTests: XCTestCase {

  func testExpectedTypeAtHole() async throws {
    // The hole's expected type is the parameter it aligns to; its own value is not constraining.
    let (types, p) = try await expectedTypes(
      in: """
        struct A { public memberwise init }

        fun f(x: A) {}

        public fun main() {
          f(hole)
        }
        """)
    XCTAssertEqual(types.map { (t) in p.show(t) }, ["A"])
  }

  func testLabeledArgumentAlignsToItsParameter() async throws {
    // A labeled hole binds the parameter carrying that label, not the one at its position: with
    // the first parameter defaulted, `f(y: _)`'s single argument is at position 0 but must be
    // aligned to the second parameter.
    let (types, p) = try await expectedTypes(
      in: """
        struct A { public memberwise init }
        struct B { public memberwise init }

        fun f(_ x: A = A(), _ y: B) {}

        public fun main() {
          f(y: hole)
        }
        """)
    XCTAssertEqual(types.map { (t) in p.show(t) }, ["B"])
  }

  func testNonViableOverloadRejectedByOtherArgument() async throws {
    // An overload is viable only if the non-hole arguments coerce to their parameters, so the
    // `B`-taking overload must not contribute an expected type when the first argument is an `A`.
    let (types, p) = try await expectedTypes(
      in: """
        struct A { public memberwise init }
        struct B { public memberwise init }

        fun f(x: A, y: A) {}
        fun f(x: B, y: B) {}

        public fun main() {
          f(A(), hole)
        }
        """)
    XCTAssertEqual(types.map { (t) in p.show(t) }, ["A"])
  }

  func testUnmetConformanceRequirementRejectsOverload() async throws {
    // Overload viability includes the candidate's context: the generic overload requires
    // `T is P`, `B` has no such given, so only the concrete overload's parameter type is
    // expected — even though plain unification would accept `T := B`.
    let (types, p) = try await expectedTypes(
      in: """
        trait P {}
        struct A { public memberwise init }
        struct B { public memberwise init }

        fun f<T is P>(x: T, y: A) {}
        fun f(x: B, y: B) {}

        public fun main() {
          f(B(), hole)
        }
        """)
    XCTAssertEqual(types.map { (t) in p.show(t) }, ["B"])
  }

  func testMetConformanceRequirementKeepsOverload() async throws {
    // The dual of the previous test: when the requirement is satisfiable the generic overload
    // stays viable and contributes its expected type. (The decoy overload keeps the callee an
    // unresolved `NameExpression`: with a single candidate the checker commits and rewrites the
    // callee into a `SyntheticExpression` even though the call itself fails to check.)
    let (types, p) = try await expectedTypes(
      in: """
        trait P {}
        struct A { public memberwise init }
        given A is P {}
        struct B { public memberwise init }

        fun f<T is P>(x: T, y: A) {}
        fun f(x: B, y: B) {}

        public fun main() {
          f(A(), hole)
        }
        """)
    XCTAssertEqual(types.map { (t) in p.show(t) }, ["A"])
  }

  // MARK: - Helpers

  /// Type-checks `source` as a single-file `Main` module and returns the expected types at the
  /// `hole` argument of the call to `f` in the file, with the program for rendering them.
  ///
  /// The hole's index is located by searching the call's argument list for the expression named
  /// `hole`, the way the LSP finds the completed node's argument — the checker may have
  /// elaborated the list, materializing defaulted arguments before the hole, so the index in the
  /// stored call can differ from the one in the written source.
  private func expectedTypes(
    in source: SourceFile,
    file: StaticString = #filePath, line: UInt = #line
  ) async throws -> ([AnyTypeIdentity], Program) {
    var p = Program()
    let m = p.demandModule(.init("Main"))
    _ = p[m].addSource(source)
    await p.assignScopes(m)
    p.assignTypes(m, loggingInferenceWhere: nil)

    // The fixture's initializer calls are `Call`s too, and the checker may have rewritten the
    // completed call's callee, so identify the call by its `hole` argument.
    func holeIndex(in c: Call.ID) -> Int? {
      p[c].arguments.firstIndex { (a) in
        p.cast(a.value, to: NameExpression.self)
          .map { (n) in p[n].name.value.identifier == "hole" } ?? false
      }
    }
    let call = try XCTUnwrap(
      p.select(.tag(Call.self))
        .compactMap { (c) in p.cast(c, to: Call.self) }
        .first { (c) in holeIndex(in: c) != nil },
      "no call with a `hole` argument in the fixture", file: file, line: line)
    let storedHoleIndex = holeIndex(in: call)!
    let scope = p.parent(containing: call)
    let types = p.expectedArgumentTypes(
      at: storedHoleIndex, ofCall: call, in: m, visibleFrom: scope)
    return (types, p)
  }

}

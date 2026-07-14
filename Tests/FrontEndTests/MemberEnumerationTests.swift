import FrontEnd
import XCTest

/// Tests for `Program.members(of:in:visibleFrom:static:)`, the member-listing query used by LSP.
final class MemberEnumerationTests: XCTestCase {

  func testEnumerateMembers() async throws {
    let names = try await instanceMembers(
      ofStruct: "A",
      in: """
      trait P { fun f() }
      struct A {
        public fun g() {}
      }
      given A is P { fun f() {} }
      extension A { fun h() {} }
      """)
    XCTAssert(names.contains("g"))  // native
    XCTAssert(names.contains("f"))  // conformance
    XCTAssert(names.contains("h"))  // extension
  }

  func testEnumerateStaticMembers() async throws {
    let names = try await staticMembers(
      ofStruct: "A",
      in: """
      trait P { static fun h() }
      struct A {
        public static fun f() {}
      }
      given A is P { public static fun h() {} }
      extension A { public static fun g() {} }
      """)
    XCTAssert(names.contains("f"))  // native
    XCTAssert(names.contains("g"))  // extension
    XCTAssert(names.contains("h"))  // conformance
  }

  func testEnumerateStaticInheritedMembers() async throws {
    // A static trait requirement is reachable only through a static selection (`A.s`), not on an
    // instance of `A`.
    let s: SourceFile = """
      trait P { static fun s() }
      struct A { }
      given A is P { public static fun s() {} }
      """

    let statics = try await staticMembers(ofStruct: "A", in: s)
    XCTAssertTrue(statics.contains("s"))

    let instance = try await instanceMembers(ofStruct: "A", in: s)
    XCTAssertFalse(instance.contains("s"))
  }

  func testIgnoreSynthesizedDeclarations() async throws {
    // The synthesized `$f` member should not be listed as a member.
    let names = try await instanceMembers(
      ofStruct: "A",
      in: """
      struct A {
        given let x: Int = 0
      }
      trait P { fun r() }
      given A is P { fun r() {} }
      extension T : P { fun h() {} }
      """)
    XCTAssert(names.contains("r"))
    XCTAssert(names.contains("h"))
    XCTAssert(names.contains("x"))
    XCTAssertFalse(names.contains(where: { $0.hasPrefix("$") }))
  }

  func testSubstitutesTypeArgumentsIntoMemberTypes() async throws {
    // Listing the members of a generic type applied to concrete arguments must substitute those
    // arguments into the reported member types: on `A<B>`, the member `f(x: T)` has type `f(x: B)`.
    var p = Program()
    let (m, f) = await typeChecked(
      &p,
      """
      struct A<T> {
        public memberwise init
        public fun f(x: T) {}
      }
      struct B { public memberwise init }
      let v = A<B>()
      """)

    let v = try XCTUnwrap(p.select(.name(.init(identifier: "v"))).first)
    let receiver = try XCTUnwrap(p.type(maybeAssignedTo: v))
    let member = try XCTUnwrap(
      p.members(of: receiver, in: m, visibleFrom: .init(file: f), resolvedStatically: false)
        .first(where: { p.name(of: $0.declaration.target!)?.identifier == "f" }))

    XCTAssertEqual(p.show(member.type), "[let A<B>](let B) let -> Void")
  }

  // MARK: - Helpers

  /// Returns the identifiers of the non-static members that `Program.members` reports for the
  /// struct named `typeName` in `source`.
  private func instanceMembers(
    ofStruct typeName: String, in source: SourceFile,
    file: StaticString = #filePath, line: UInt = #line
  ) async throws -> Set<String> {
    try await members(ofStruct: typeName, in: source, static: false, file: file, line: line)
  }

  /// Returns the identifiers of the static members that `Program.members` reports for the struct 
  /// named `name` in `source`.
  private func staticMembers(
    ofStruct name: String, in source: SourceFile,
    file: StaticString = #filePath, line: UInt = #line
  ) async throws -> Set<String> {
    try await members(ofStruct: name, in: source, static: true, file: file, line: line)
  }

  /// Type-checks `source` as a single-file module and returns the identifiers of the members
  /// of the struct named `typeName`, selecting static members iff `isStatic` is `true`.
  private func members(
    ofStruct typeName: String, in source: SourceFile, static isStatic: Bool,
    file: StaticString, line: UInt
  ) async throws -> Set<String> {
    var p = Program()
    let (m, f) = await typeChecked(&p, source)

    let d = try XCTUnwrap(
      p.select(.and(.tag(StructDeclaration.self), .name(.init(identifier: typeName)))).first,
      "no struct named '\(typeName)'", file: file, line: line)
    // The type assigned to a struct declaration is its metatype; `members` normalizes that to the
    // instance type and selects static or instance members per the flag.
    let receiver = p.type(assignedTo: d)
    return Set(
      p.members(of: receiver, in: m, visibleFrom: .init(file: f), resolvedStatically: isStatic)
        .compactMap({ p.name(of: $0.declaration.target!)?.identifier }))
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

import FrontEnd
import XCTest

/// Tests for `Program.members(of:in:visibleFrom:static:)`, the member-listing query used by LSP.
final class MemberListingTests: XCTestCase {

  func testListsNativeConformanceAndExtensionMembers() async throws {
    // An instance receiver should see its own members, the members of an applicable extension, and
    // the requirements of every trait it conforms to.
    let names = try await instanceMembers(
      ofStruct: "A",
      in: """
      trait P { fun f() }
      struct A {
        public memberwise init
        public fun g() {}
      }
      given A is P { fun f() {} }
      extension A { fun h() {} }
      """)
    XCTAssert(names.contains("g"))  // native
    XCTAssert(names.contains("f"))  // conformance
    XCTAssert(names.contains("h"))  // extension
  }

  func testListsStaticMembersFromAllSources() async throws {
    // A type receiver should see static members from the type itself, an extension, and a
    // conformance.
    let names = try await staticMembers(
      ofStruct: "A",
      in: """
      trait P { static fun h() }
      struct A {
        public memberwise init
        public static fun f() {}
      }
      given A is P { public static fun h() {} }
      extension A { public static fun g() {} }
      """)
    XCTAssert(names.contains("f"))  // native
    XCTAssert(names.contains("g"))  // extension
    XCTAssert(names.contains("h"))  // conformance
  }

  func testStaticConformanceRequirementRequiresStaticSelection() async throws {
    // A static trait requirement is reachable only through a static selection (`A.s`), not on an
    // instance, so the `static` flag must be honored in the conformance branch.
    let source: SourceFile = """
      trait P { static fun s() }
      struct A { public memberwise init }
      given A is P { public static fun s() {} }
      """
    let statics = try await staticMembers(ofStruct: "A", in: source)
    let instance = try await instanceMembers(ofStruct: "A", in: source)
    XCTAssertTrue(statics.contains("s"))
    XCTAssertFalse(instance.contains("s"))
  }

  func testDoesNotListSynthesizedConformanceWitnesses() async throws {
    // The synthesized `$f` member should not be listed as a member.
    let names = try await instanceMembers(
      ofStruct: "A",
      in: """
      struct A {
        public memberwise init
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
      p.members(of: receiver, in: m, visibleFrom: .init(file: f), static: false)
        .first(where: { p.name(of: $0.declaration)?.identifier == "f" }))

    XCTAssertEqual(p.show(member.type), "[let A<B>](let B) let -> Void")
  }

  func testTypeOfSelfIsTheEnclosingTypeWithinAStructScope() async throws {
    // "Self" inside a struct's body denotes an instance of that struct.
    var p = Program()
    let _ = await typeChecked(
      &p,
      """
      struct A {
        public memberwise init
      }
      """)

    let d = try XCTUnwrap(
      p.select(.and(.tag(StructDeclaration.self), .name(.init(identifier: "A")))).first,
      "no struct named 'A'")
    let selfType = try XCTUnwrap(p.typeOfSelf(in: .init(uncheckedFrom: d.erased)))
    XCTAssertEqual(p.show(selfType), "A")
  }

  func testTypeOfSelfIsNilAtFileScope() async throws {
    // "Self" is not legal at the top level of a file, where no type encloses the use.
    var p = Program()
    let (_, f) = await typeChecked(
      &p,
      """
      struct A {
        public memberwise init
      }
      """)

    XCTAssertNil(p.typeOfSelf(in: .init(file: f)))
  }

  // MARK: - Helpers

  /// Returns the identifiers of the members `Program.members` reports for the struct named
  /// `typeName` declared in `source`, selecting instance members.
  private func instanceMembers(
    ofStruct typeName: String, in source: SourceFile,
    file: StaticString = #filePath, line: UInt = #line
  ) async throws -> Set<String> {
    try await memberNames(ofStruct: typeName, in: source, static: false, file: file, line: line)
  }

  /// Returns the identifiers of the members `Program.members` reports for the struct named `name`
  /// declared in `source`, selecting static members.
  private func staticMembers(
    ofStruct name: String, in source: SourceFile,
    file: StaticString = #filePath, line: UInt = #line
  ) async throws -> Set<String> {
    try await memberNames(ofStruct: name, in: source, static: true, file: file, line: line)
  }

  /// Type-checks `source` as a single-file module and returns the identifiers of the members
  /// reported for the struct named `typeName`, selecting static members iff `isStatic`.
  private func memberNames(
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
      p.members(of: receiver, in: m, visibleFrom: .init(file: f), static: isStatic)
        .compactMap({ p.name(of: $0.declaration)?.identifier }))
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

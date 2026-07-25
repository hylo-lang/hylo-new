import FrontEnd
import XCTest

@testable import Interpreter

final class TypeLayoutTests: XCTestCase {

  var p = Program(forTesting: true)
  var l = TypeLayoutCache(for: UnrealABI())

  func check(layoutOf t: MachineType, hasSize s: Int, andAlignment a: Int) {
    let r = layout(p.types.demand(t).erased)
    XCTAssertEqual(r.size, s)
    XCTAssertEqual(r.alignment, a)
    XCTAssert(r.parts.isEmpty)
  }

  func testBuiltinIntegers() throws {
    check(layoutOf: .i(1), hasSize: 1, andAlignment: 1)
    check(layoutOf: .i(8), hasSize: 1, andAlignment: 1)
    check(layoutOf: .i(16), hasSize: 2, andAlignment: 2)
    check(layoutOf: .i(32), hasSize: 4, andAlignment: 4)
    check(layoutOf: .i(64), hasSize: 8, andAlignment: 8)
  }

  func testTrivialTuples() throws {
    let void = layout(p.types.tuple(of: []))
    XCTAssertEqual(void.size, 0)
    XCTAssertEqual(void.alignment, 1)
    XCTAssert(void.parts.isEmpty)

    let i8 = id(MachineType.i(8))
    let justI8 = layout(p.types.tuple(of: [i8]))
    XCTAssertEqual(justI8.size, 1)
    XCTAssertEqual(justI8.alignment, 1)
    XCTAssertEqual(justI8.parts, [.init(name: "0", type: .init(i8), offset: 0)])
  }

  func testPairs() throws {
    let i8 = id(MachineType.i(8))
    let i64 = id(MachineType.i(64))
    let i8i64 = layout(p.types.tuple(of: [i8, i64]))
    XCTAssertEqual(i8i64.bytes, .init(alignment: 8, size: 16))
    let i64i8 = layout(p.types.tuple(of: [i64, i8]))
    XCTAssertEqual(i64i8.bytes, .init(alignment: 8, size: 9))

    XCTAssertEqual(
      i8i64.parts,
      [
        .init(name: "0", type: .init(i8), offset: 0),
        .init(name: "1", type: .init(i64), offset: 8),
      ])

    XCTAssertEqual(
      i64i8.parts,
      [
        .init(name: "0", type: .init(i64), offset: 0),
        .init(name: "1", type: .init(i8), offset: 8),
      ])
  }

  func testTriple() {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))
    let i32 = id(MachineType.i(32))

    let i8i16i32 = layout(p.types.tuple(of: [i8, i16, i32]))
    XCTAssertEqual(i8i16i32.bytes, .init(alignment: 4, size: 8))

    XCTAssertEqual(
      i8i16i32.parts,
      [
        .init(name: "0", type: .init(i8), offset: 0),
        .init(name: "1", type: .init(i16), offset: 2),
        .init(name: "2", type: .init(i32), offset: 4),
      ])
  }

  func testEmptyStruct() async throws {
    let emptyStruct = layout(
      await type(
        named: "EmptyStruct",
        in: """
          public struct EmptyStruct {}
          """))

    XCTAssertEqual(emptyStruct.size, 0)
    XCTAssertEqual(emptyStruct.alignment, 1)
    XCTAssert(emptyStruct.parts.isEmpty)
  }

  func testPairStruct() async throws {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))

    let i816 = layout(
      await type(
        named: "PairStruct",
        in: """
          public struct PairStruct {
            let x: Builtin.i8
            let y: Builtin.i16
          }
          """))

    XCTAssertEqual(i816.size, 4)
    XCTAssertEqual(i816.alignment, 2)
    XCTAssertEqual(
      i816.parts,
      [
        .init(name: "x", type: .init(i8), offset: 0),
        .init(name: "y", type: .init(i16), offset: 2),
      ])
  }

  func testEmptyEnum() async throws {
    let emptyEnum = layout(
      await type(
        named: "EmptyEnum",
        in: """
          public enum EmptyEnum {}
          """))

    XCTAssertEqual(emptyEnum.size, 0)
    XCTAssertEqual(emptyEnum.alignment, 1)
    XCTAssertEqual(
      emptyEnum.parts,
      [.init(name: "discriminator", type: .init(.void), offset: 0)])
  }

  func testOptionalEnum() async throws {
    let optional = layout(
      await type(
        named: "Optional",
        in: """
          public enum Optional {
            case some(wrapped: Builtin.i16)
            case none
          }
          """))

    let i8 = id(MachineType.i(8))
    let i16Tuple = p.types.tuple(of: [id(MachineType.i(16))])

    XCTAssertEqual(optional.size, 3)
    XCTAssertEqual(optional.alignment, 2)
    XCTAssertEqual(
      optional.parts,
      [
        .init(name: "some", type: .init(i16Tuple), offset: 0),
        .init(name: "none", type: .init(.void), offset: 0),
        .init(name: "discriminator", type: .init(i8), offset: 2),
      ])
  }

  /// Returns type declared as `n` in `s`.
  ///
  /// - Precondition: `n` should be unique across `p`.
  /// - Precondition: `n` should be present in `s`.
  private func type(named n: String, in s: SourceFile) async -> AnyTypeIdentity {
    await add(s)
    let d = p.castToDeclaration(p.select(.name(.init(identifier: n))).first!)!
    let mt = p.type(assignedTo: d, assuming: Metatype.self)
    return p.types[mt].inhabitant
  }

  /// Adds `s` with no dependency to `p`.
  private func add(_ s: SourceFile) async {
    let name = UUID().uuidString
    let m = p.demandModule(Module.Name(name))
    _ = p[m].addSource(s)
    await p.assignScopes(m)
    p.assignTypes(m) { _, _ in false }
  }

  /// Returns the type erased identity of `t`.
  private func id<T: TypeTree>(_ t: T) -> AnyTypeIdentity {
    p.types.demand(t).erased
  }

  /// Returns the layout of `t`.
  private func layout(_ t: AnyTypeIdentity) -> TypeLayout {
    l.layout(.init(t), in: &p)
  }

}

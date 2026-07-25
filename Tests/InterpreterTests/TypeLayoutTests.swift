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
        named: "OptionalInt",
        in: """
          public enum OptionalInt {
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

  func testTypeAlias() async throws {
    let int8 = layout(
      await type(
        named: "Int8",
        in: """
          public type I8 = Builtin.i8
          public type Int8 = I8
          """))

    XCTAssertEqual(int8.size, 1)
    XCTAssertEqual(int8.alignment, 1)
    XCTAssert(int8.parts.isEmpty)
  }

  func testStructWithTypeApplication() async throws {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))

    let i816 = layout(
      await type(
        named: "Pair",
        appliedTo: [i8, i16],
        in: """
          public struct Pair<T, U> {
            let x: T
            let y: U
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

  func testEnumWithTypeApplication() async throws {
    let i16 = id(MachineType.i(16))

    let optional = layout(
      await type(
        named: "Optional",
        appliedTo: [i16],
        in: """
          public enum Optional<T> {
            case some(wrapped: T)
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

  // TODO: uncomment when raw enum representation gets supported.
  //
  // func testRawEnum() async throws {
  //   let color = layout(
  //     await type(
  //       named: "Color",
  //       in: """
  //         public enum Color(Int) {
  //           case red = 0
  //           case blue = 1
  //         }
  //         """))
  //
  //   let i8 = id(MachineType.i(8))
  //
  //   XCTAssertEqual(color.size, 3)
  //   XCTAssertEqual(color.alignment, 2)
  //   XCTAssertEqual(
  //     color.parts,
  //     [
  //       .init(name: "discriminator", type: .init(i8), offset: 0)
  //     ])
  // }

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

  /// Returns `n<arguments...>` declared in `s`.
  private func type(
    named n: String, appliedTo arguments: [AnyTypeIdentity],
    in s: SourceFile
  ) async -> AnyTypeIdentity {
    let u = await type(named: n, in: s)
    let f = p.types.cast(u, to: UniversalType.self)!
    return p.types.application(of: f, to: arguments)
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

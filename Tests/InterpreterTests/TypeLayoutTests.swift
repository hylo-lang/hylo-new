import FrontEnd
import XCTest
import Utilities

@testable import Interpreter

final class TypeLayoutTests: XCTestCase {

  var p = Program(forTesting: true)
  var l = TypeLayoutCache(for: UnrealABI())

  func check(layoutOf t: MachineType, hasSize s: Int, andAlignment a: Alignment) {
    let r = layout(p.types.demand(t).erased)
    XCTAssertEqual(r.size, s)
    XCTAssertEqual(r.alignment, a)
    XCTAssert(r.parts.isEmpty)
  }

  func testBuiltinIntegers() throws {
    check(layoutOf: .i(1), hasSize: 1, andAlignment: .bytes(1))
    check(layoutOf: .i(8), hasSize: 1, andAlignment: .bytes(1))
    check(layoutOf: .i(16), hasSize: 2, andAlignment: .bytes(2))
    check(layoutOf: .i(32), hasSize: 4, andAlignment: .bytes(4))
    check(layoutOf: .i(64), hasSize: 8, andAlignment: .bytes(8))
  }

  func testTrivialTuples() throws {
    let void = layout(.void)
    XCTAssertEqual(void.size, 0)
    XCTAssertEqual(void.alignment, .bytes(1))
    XCTAssert(void.parts.isEmpty)

    let i8 = id(MachineType.i(8))
    let justI8 = layout(p.types.tuple(of: [i8]))
    XCTAssertEqual(justI8.size, 1)
    XCTAssertEqual(justI8.alignment, .bytes(1))
    XCTAssertEqual(justI8.parts, [.init(name: "0", type: .init(i8), offset: 0)])
  }

  func testPairs() throws {
    let i8 = id(MachineType.i(8))
    let i64 = id(MachineType.i(64))
    let i8i64 = layout(p.types.tuple(of: [i8, i64]))
    XCTAssertEqual(i8i64.footprint, .init(alignment: .bytes(8), size: 9))
    let i64i8 = layout(p.types.tuple(of: [i64, i8]))
    XCTAssertEqual(i64i8.footprint, .init(alignment: .bytes(8), size: 9))

    XCTAssertEqual(
      i8i64.parts,
      [
        .init(name: "0", type: .init(i8), offset: 8),
        .init(name: "1", type: .init(i64), offset: 0),
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
    XCTAssertEqual(i8i16i32.footprint, .init(alignment: .bytes(4), size: 7))

    XCTAssertEqual(
      i8i16i32.parts,
      [
        .init(name: "0", type: .init(i8), offset: 6),
        .init(name: "1", type: .init(i16), offset: 4),
        .init(name: "2", type: .init(i32), offset: 0),
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
    XCTAssertEqual(emptyStruct.alignment, .bytes(1))
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

    XCTAssertEqual(i816.size, 3)
    XCTAssertEqual(i816.alignment, .bytes(2))
    XCTAssertEqual(
      i816.parts,
      [
        .init(name: "x", type: .init(i8), offset: 2),
        .init(name: "y", type: .init(i16), offset: 0),
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
    XCTAssertEqual(emptyEnum.alignment, .bytes(1))
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
    XCTAssertEqual(optional.alignment, .bytes(2))
    XCTAssertEqual(
      optional.parts,
      [
        .init(name: "some", type: .init(i16Tuple), offset: 0),
        .init(name: "none", type: .init(.void), offset: 0),
        .init(name: "discriminator", type: .init(i8), offset: 2),
      ])
  }

  func testMachineTypeAlias() async throws {
    let int8 = layout(
      await type(
        named: "Int8",
        in: """
          public type I8 = Builtin.i8
          public type Int8 = I8
          """))

    XCTAssertEqual(int8.size, 1)
    XCTAssertEqual(int8.alignment, .bytes(1))
    XCTAssert(int8.parts.isEmpty)
  }

  func testTupleTypeAlias() async throws {
    let i8Tuple = layout(
      await type(
        named: "I8Tuple",
        in: """
          public type I8Tuple_ = {Builtin.i8}
          public type I8Tuple = I8Tuple_
          """))

    let i8 = id(MachineType.i(8))
    XCTAssertEqual(i8Tuple.size, 1)
    XCTAssertEqual(i8Tuple.alignment, .bytes(1))
    XCTAssertEqual(
      i8Tuple.parts,
      [
        .init(name: "0", type: .init(i8), offset: 0)
      ])
  }

  func testStructTypeAlias() async throws {
    let i8Struct = layout(
      await type(
        named: "I8Struct",
        in: """
          public struct I8Struct__ {
            let x: Builtin.i8
          }
          public type I8Struct_ = I8Struct__
          public type I8Struct = I8Struct_
          """))

    let i8 = id(MachineType.i(8))
    XCTAssertEqual(i8Struct.size, 1)
    XCTAssertEqual(i8Struct.alignment, .bytes(1))
    XCTAssertEqual(
      i8Struct.parts,
      [
        .init(name: "x", type: .init(i8), offset: 0)
      ])
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

    XCTAssertEqual(i816.size, 3)
    XCTAssertEqual(i816.alignment, .bytes(2))
    XCTAssertEqual(
      i816.parts,
      [
        .init(name: "x", type: .init(i8), offset: 2),
        .init(name: "y", type: .init(i16), offset: 0),
      ])
  }

  func testTupleWithTypeApplication() async throws {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))

    let i816 = layout(
      await type(
        named: "PairTuple",
        appliedTo: [i8, i16],
        in: """
          type PairTuple<T, U> = {T, U}
          """))

    XCTAssertEqual(i816.size, 3)
    XCTAssertEqual(i816.alignment, .bytes(2))
    XCTAssertEqual(
      i816.parts,
      [
        .init(name: "0", type: .init(i8), offset: 2),
        .init(name: "1", type: .init(i16), offset: 0),
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
    XCTAssertEqual(optional.alignment, .bytes(2))
    XCTAssertEqual(
      optional.parts,
      [
        .init(name: "some", type: .init(i16Tuple), offset: 0),
        .init(name: "none", type: .init(.void), offset: 0),
        .init(name: "discriminator", type: .init(i8), offset: 2),
      ])
  }

  func testNestedAliasedGenericTuple() async throws {
    let t = layout(
      await type(
        named: "Chained",
        in: """
          public type CA<T> = {T}
          public type Chained = CA<CA<CA<Builtin.i16>>>
          """))

    let i16 = id(MachineType.i(16))
    let tInner = p.types.tuple(of: [i16])
    let tMiddle = p.types.tuple(of: [tInner])

    XCTAssertEqual(t.size, 2)
    XCTAssertEqual(t.alignment, .bytes(2))
    XCTAssertEqual(t.parts, [.init(name: "0", type: .init(tMiddle), offset: 0)])
  }

  func testEnumDiscriminator() {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))
    let i32 = id(MachineType.i(32))

    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 1, in: &p).underlying, .void)
    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 2, in: &p).underlying, i8)
    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 8, in: &p).underlying, i8)
    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 256, in: &p).underlying, i8)
    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 257, in: &p).underlying, i16)
    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 65536, in: &p).underlying, i16)
    XCTAssertEqual(UnrealABI().enumDiscriminator(count: 65537, in: &p).underlying, i32)
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
  //   XCTAssertEqual(color.alignment, .bytes(2))
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
    let mt = p.types.cast(p.type(maybeAssignedTo: d)!, to: Metatype.self)!
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

  private func check_offsets(members sa: [TypeLayout.StorageRequirements]) {
    if sa.count == 0 { return }
    let l = storageLayoutOfRecord(havingMembers: sa)
    let offsets = l.partOffsets

    // Zero-sized members don't influence the layout. Nothing is guaranteed about their offsets.
    let nonEmpty = sa.indices.filter { sa[$0].size != 0 }
    let withoutEmpty = storageLayoutOfRecord(havingMembers: nonEmpty.map { sa[$0] })
    XCTAssertEqual(nonEmpty.map { offsets[$0] }, withoutEmpty.partOffsets)
    XCTAssertEqual(l.footprint, withoutEmpty.footprint)

    let member_order = nonEmpty.sorted { (i, j) in
      offsets[i] < offsets[j]
        || offsets[i] == offsets[j] && sa[i].alignment > sa[j].alignment
    }
    if member_order.isEmpty { return }

    // First member always sits at offset 0
    XCTAssertEqual(offsets[member_order.first!], 0)
    for (i0, i1) in zip(member_order, member_order.dropFirst()) {
      let (m0, o0) = (sa[i0], offsets[i0])
      let (m1, o1) = (sa[i1], offsets[i1])
      XCTAssertGreaterThanOrEqual(
        m0.alignment, m1.alignment,
        """
        Member \(i0) with alignment \(m0.alignment) ordered before member \(i1)
        with alignment \(m1.alignment)!
        \(zip(sa, offsets).map { "\n\($0), offset: \($1)" }.joined())
        """
      )
      if m0.alignment == m1.alignment {
        XCTAssertLessThan(
          i0, i1,
          """
          Members \(i0) and \(i1) with the same alignment are out of order!
          \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
          """
        )

      }
      XCTAssertGreaterThanOrEqual(
        m0.alignment, m1.alignment,
        """
        Increasing alignment between consecutive members \(i0) and \(i1)!
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )

      XCTAssert(
        o1.isMultiple(of: m1.alignment),
        """
          member \(i1) at offset \(o1) not aligned to \(m1.alignment)!
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )

      let end0 = o0 + m0.size
      XCTAssertLessThanOrEqual(
        end0, o1,
        """
        member \(i1) at offset \(o1) overlaps preceding member \(i0) at \(o0)!
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )
      let padding = o1 &- end0

      XCTAssertLessThan(
        padding, m1.alignment.bytes,
        """
        Needless padding \(padding) before member at offset \(o1)
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """)
    }
  }

  func testOffsetOfMember() {

    check_offsets(members: [
      .init(alignment: .bytes(1), size: 5),
      .init(alignment: .bytes(2), size: 3),
      .init(alignment: .bytes(8), size: 5),
    ])
    check_offsets(members: [
      .init(alignment: .bytes(4), size: 7),
      .init(alignment: .bytes(8), size: 5),
      .init(alignment: .bytes(1), size: 0),
      .init(alignment: .bytes(4), size: 9),
      .init(alignment: .bytes(16), size: 1),
    ])

    var g = SeedableRandomNumberGenerator(seed: 42)
    for _ in 0..<3 {
      let a = (0..<1).map { _ in randomStorageRequirements(using: &g) }
      check_offsets(members: a)
    }
    for _ in 0..<100 {
      let a = (0..<2).map { _ in randomStorageRequirements(using: &g) }
      check_offsets(members: a)
    }

    for _ in 0..<2000 {
      let a = (0..<10).map { _ in randomStorageRequirements(using: &g) }
      check_offsets(members: a)
    }
  }

  /// Returns random storage requirements, of alignment 1 if the size is zero.
  private func randomStorageRequirements<R: RandomNumberGenerator>(
    using g: inout R
  ) -> TypeLayout.StorageRequirements {
    let s = Int.random(in: 0..<10, using: &g)
    let a = s == 0 ? Alignment(log2: 0) : Alignment(log2: UInt8.random(in: 0..<5, using: &g))
    return .init(alignment: a, size: s)
  }

  func testBytesOfStorageLayoutOfRecord() {
    XCTAssertEqual(
      storageLayoutOfRecord(havingMembers: [
        .init(alignment: .bytes(1), size: 5), .init(alignment: .bytes(2), size: 3),
        .init(alignment: .bytes(1), size: 0), .init(alignment: .bytes(8), size: 5),
      ]).footprint,

      .init(alignment: .bytes(8), size: 14)
    )
  }

  func testLocationOfField() async throws {
    let t = await type(
      named: "I8I16Struct",
      in: """
        public struct I8I16Struct {
          let x: Builtin.i8
          let y: Builtin.i16
        }
        """
    )
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))

    var m = Memory(forRunning: p, on: UnrealABI())
    let a = m.allocate(storageFor: t).asTypedAddress(t)

    XCTAssertGreaterThan(m.layout(i16).alignment, m.layout(i8).alignment)

    XCTAssertEqual(
      m.location(ofField: "x", in: a),
      .init(allocation: a.allocation, offset: 2, type: .init(i8)))

    XCTAssertEqual(
      m.location(ofField: "y", in: a),
      .init(allocation: a.allocation, offset: 0, type: .init(i16)))
  }
}

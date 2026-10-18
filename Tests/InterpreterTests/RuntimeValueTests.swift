import FrontEnd
import XCTest

@testable import Interpreter

final class RuntimeValueTests: XCTestCase {

  var p = Program(forTesting: true)
  var l = LayoutComputer(for: UnrealABI())

  func testBool() {
    let i1 = id(MachineType.i(1))
    XCTAssertEqual(
      RuntimeValue(bool: true)
        .byteRepresentation(asValueOf: i1, definedIn: &p, laidOutUsing: &l),
      [1]
    )
    XCTAssertEqual(
      RuntimeValue(bool: false)
        .byteRepresentation(asValueOf: i1, definedIn: &p, laidOutUsing: &l),
      [0]
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i1, definedIn: &p,
        havingByteRepresentation: [0][...], providedBy: &l
      ).byteRepresentation(asValueOf: i1, definedIn: &p, laidOutUsing: &l),
      [0]
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i1, definedIn: &p,
        havingByteRepresentation: [1][...], providedBy: &l
      ).byteRepresentation(asValueOf: i1, definedIn: &p, laidOutUsing: &l),
      [1]
    )
  }

  func testInteger() {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))
    let i32 = id(MachineType.i(32))
    let i64 = id(MachineType.i(64))
    let i128 = id(MachineType.i(128))

    var bs: [UInt8] = [2]
    XCTAssertEqual(
      RuntimeValue(integer: 2, bitWidth: 8)
        .byteRepresentation(asValueOf: i8, definedIn: &p, laidOutUsing: &l),
      bs
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i8, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: i8, definedIn: &p, laidOutUsing: &l),
      bs
    )

    bs = [2, 1]
    XCTAssertEqual(
      RuntimeValue(integer: 258, bitWidth: 16)
        .byteRepresentation(asValueOf: i16, definedIn: &p, laidOutUsing: &l),
      bs
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i16, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: i16, definedIn: &p, laidOutUsing: &l),
      bs
    )

    bs = [2, 1, 0, 0]
    XCTAssertEqual(
      RuntimeValue(integer: 258, bitWidth: 32)
        .byteRepresentation(asValueOf: i32, definedIn: &p, laidOutUsing: &l),
      bs
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i32, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: i32, definedIn: &p, laidOutUsing: &l),
      bs
    )

    bs = [2, 1, 0, 0, 0, 0, 0, 0]
    XCTAssertEqual(
      RuntimeValue(integer: 258, bitWidth: 64)
        .byteRepresentation(asValueOf: i64, definedIn: &p, laidOutUsing: &l),
      bs
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i64, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: i64, definedIn: &p, laidOutUsing: &l),
      bs
    )

    bs = [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    XCTAssertEqual(
      RuntimeValue(integer: 258, bitWidth: 128)
        .byteRepresentation(asValueOf: i128, definedIn: &p, laidOutUsing: &l),
      bs
    )
    XCTAssertEqual(
      RuntimeValue(
        ofType: i128, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: i128, definedIn: &p, laidOutUsing: &l),
      bs
    )
  }

  func testTuple() {
    let i8 = id(MachineType.i(8))
    let i16 = id(MachineType.i(16))
    let inner = p.types.tuple(of: [i8.underlying, i16.underlying])
    let t = MonomorphicTypeIdentity(p.types.tuple(of: [i8.underlying, inner]))
    let bs: [UInt8] = [3, 0, 2, 1]
    XCTAssertEqual(
      RuntimeValue(
        ofType: t, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: t, definedIn: &p, laidOutUsing: &l),
      bs
    )
  }

  func testStruct() async throws {
    let t = await type(
      named: "I8I16I8",
      in: """
        public struct I16I8 {
          let x: Builtin.i16
          let y: Builtin.i8
        }
        public struct I8I16I8 {
          let x: Builtin.i8
          let y: I16I8
        }
        """
    )
    let bs: [UInt8] = [2, 0, 3, 1]
    XCTAssertEqual(
      RuntimeValue(
        ofType: t, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: t, definedIn: &p, laidOutUsing: &l),
      bs
    )
  }

  func testEnum() async throws {
    let t = await type(
      named: "Either",
      in: """
        public enum Either {
          case first(value: Builtin.i8)
          case second(value: Builtin.i16)
        }
        """
    )
    var bs: [UInt8] = [2, 0, 1]
    XCTAssertEqual(
      RuntimeValue(
        ofType: t, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: t, definedIn: &p, laidOutUsing: &l),
      bs
    )

    bs = [2, 0, 0]
    XCTAssertEqual(
      RuntimeValue(
        ofType: t, definedIn: &p,
        havingByteRepresentation: bs[...], providedBy: &l
      ).byteRepresentation(asValueOf: t, definedIn: &p, laidOutUsing: &l),
      bs
    )
  }

  /// Returns the type erased identity of `t`.
  private func id<T: TypeTree>(_ t: T) -> MonomorphicTypeIdentity {
    .init(p.types.demand(t).erased)
  }

  /// Returns type declared as `n` in `s`.
  ///
  /// - Precondition: `n` should be unique across `p`.
  /// - Precondition: `n` should be present in `s`.
  private func type(named n: String, in s: SourceFile) async -> MonomorphicTypeIdentity {
    await add(s)
    let d = p.castToDeclaration(p.select(.name(.init(identifier: n))).first!)!
    let mt = p.types.cast(p.type(maybeAssignedTo: d)!, to: Metatype.self)!
    return .init(p.types[mt].inhabitant)
  }

  /// Adds `s` with no dependency to `p`.
  private func add(_ s: SourceFile) async {
    let name = UUID().uuidString
    let m = p.demandModule(Module.Name(name))
    _ = p[m].addSource(s)
    await p.assignScopes(m)
    p.assignTypes(m) { _, _ in false }
  }

}

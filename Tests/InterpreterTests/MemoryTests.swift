import FrontEnd
import XCTest

@testable import Interpreter

final class InterpreterMemoryTests: XCTestCase {

  var m = Memory(forRunning: .init(forTesting: true), on: UnrealABI())
  var l = TypeLayoutCache(for: UnrealABI())

  func testAllocation() throws {
    var allocations: [Memory.Address] = []
    for sizeInBits in [8, 16, 32, 64, 128] {
      let t = MachineType.i(UInt8(sizeInBits))
      let alignment = layout(id(t)).alignment
      let p = m.allocate(.init(id(t)))
      allocations.append(p)
      XCTAssertEqual(m[p.allocation].size, sizeInBits / 8, "alignment \(alignment)")
      XCTAssert(m.address(p, hasAlignment: alignment))
    }

    for p in allocations {
      try m.deallocate(p)

      check(throws: Memory.Error.noLongerAllocated(p)) { try m.deallocate(p) }

      let q = p + 1
      check(throws: Memory.Error.deallocationNotAtStartOfAllocation(q)) { try m.deallocate(q) }
    }
  }

  func testMemoryAddressArithmetic() throws {
    let a = m.allocate(.init(id(MachineType.i(8))), count: 128)

    XCTAssertEqual(a + 1, .init(allocation: a.allocation, offset: a.offset + 1))
    XCTAssertEqual(1 + a, .init(allocation: a.allocation, offset: a.offset + 1))
    XCTAssertEqual(a + 1 - 1, a)

    var b = a
    b += 1
    XCTAssertEqual(b, .init(allocation: a.allocation, offset: a.offset + 1))
    b -= 1
    XCTAssertEqual(b, a)
  }

  func testSubPart() {
    let i8 = id(MachineType.i(8))
    let i32 = id(MachineType.i(32))
    let inner = m.program.types.tuple(of: [i8, i32])
    let t = m.program.types.tuple(of: [i32, inner])

    let a = m.allocate(.init(t))
    let p = Memory.TypedAddress(
      allocation: a.allocation, offset: a.offset, type: .init(t))

    XCTAssertEqual(
      m.location([], in: p),
      .init(allocation: a.allocation, offset: a.offset, type: .init(t)))

    XCTAssertEqual(
      m.location([0], in: p),
      .init(allocation: a.allocation, offset: a.offset, type: .init(i32)))

    XCTAssertEqual(
      m.location([1], in: p),
      .init(allocation: a.allocation, offset: a.offset + 4, type: .init(inner)))

    XCTAssertEqual(
      m.location([1, 0], in: p),
      .init(allocation: a.allocation, offset: a.offset + 8, type: .init(i8)))

    XCTAssertEqual(
      m.location([1, 1], in: p),
      .init(allocation: a.allocation, offset: a.offset + 4, type: .init(i32)))
  }

  /// Returns the type erased identity of `t`.
  private func id<T: TypeTree>(_ t: T) -> AnyTypeIdentity {
    m.program.id(t)
  }

  /// Returns the layout of `t`.
  private func layout(_ t: AnyTypeIdentity) -> TypeLayout {
    return l.layout(.init(t), in: &m.program)
  }

}

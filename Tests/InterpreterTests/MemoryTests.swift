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

  /// Returns the type erased identity of `t`.
  private func id<T: TypeTree>(_ t: T) -> AnyTypeIdentity {
    m.program.types.demand(t).erased
  }

  /// Returns the layout of `t`.
  private func layout(_ t: AnyTypeIdentity) -> TypeLayout {
    return l.layout(.init(t), in: &m.program)
  }

}

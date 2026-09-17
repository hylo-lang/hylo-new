import FrontEnd
import XCTest

@testable import Interpreter

final class InterpreterMemoryInternalTests: XCTestCase {

  func testReadingAndWritingToMemory() throws {
    var m = Memory(forRunning: .init(forTesting: true), on: UnrealABI())

    let i1 = m.program.id(MachineType.i(1))
    var a = m.allocate(storageFor: i1).asTypedAddress(i1)
    m[a] = RuntimeValue(bool: true)
    XCTAssertEqual(m[a].asBool, true)

    let i16 = m.program.id(MachineType.i(16))
    a = m.allocate(storageFor: i16).asTypedAddress(i16)
    m[a] = RuntimeValue(integer: 16, bitWidth: 16, byteOrder: .little)
    XCTAssertEqual(m[a].asI16(assumingByteOrder: .little), 16)
  }

  func testCheckAlignmentAndAllocationBounds() throws {
    var m = Memory(forRunning: .init(forTesting: true), on: UnrealABI())
    let i8 = m.program.id(MachineType.i(8))
    let i16 = m.program.id(MachineType.i(16))
    let l = m.typeLayouts.layout(.init(i16), in: &m.program)
    let a = m.allocate(.init(i8), count: 31)
    try m[a.allocation].checkAlignmentAndAllocationBounds(at: 0, for: l)
    check(throws: Memory.Error.alignment(a + 1, for: l)) {
      try m[a.allocation].checkAlignmentAndAllocationBounds(at: 1, for: l)
    }
    check(throws: Memory.Error.bounds(a + 30, for: l, allocationSize: 31)) {
      try m[a.allocation].checkAlignmentAndAllocationBounds(at: 30, for: l)
    }
  }

}

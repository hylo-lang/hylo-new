import FrontEnd
import XCTest

@testable import Interpreter

final class InterpreterMemoryInternalTests: XCTestCase {

  func testFormingPointerToLastByteOfAllocation() throws {
    var m = Memory(forRunning: .init(forTesting: true), on: UnrealABI())
    let a = m.allocate(.init(m.program.id(MachineType.i(8))))

    m[a.allocation].withUnsafeMutablePointer(to: UInt8.self, at: 0) { p in
      p.pointee = 2
    }
    m[a.allocation].withUnsafePointer(to: UInt8.self, at: 0) { p in
      XCTAssertEqual(p.pointee, 2)
    }

  }

  func testFormingPointerToOneByteLaterThanLastByteOfAllocation() throws {
    var m = Memory(forRunning: .init(forTesting: true), on: UnrealABI())
    let a = m.allocate(.init(m.program.id(MachineType.i(8))))

    m[a.allocation].withUnsafeMutablePointer(to: Void.self, at: 1) { _ = $0 }
    m[a.allocation].withUnsafePointer(to: Void.self, at: 1) { _ = $0 }
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

  func testUnsignnedIntValue() throws {
    var m = Memory(forRunning: .init(forTesting: true), on: UnrealABI())
    let a = m.allocate(.init(m.program.id(MachineType.i(8))), count: 64)
    m[a.allocation].withUnsafeMutablePointer(to: UInt8.self, at: 0) { p in
      p.pointee = 8
    }
    XCTAssertEqual(m[a.allocation].unsignedIntValue(at: 0, ofType: .i(8)), 8)

    m[a.allocation].withUnsafeMutablePointer(to: UInt16.self, at: 0) { p in
      p.pointee = 16
    }
    XCTAssertEqual(m[a.allocation].unsignedIntValue(at: 0, ofType: .i(16)), 16)

    m[a.allocation].withUnsafeMutablePointer(to: UInt32.self, at: 0) { p in
      p.pointee = 32
    }
    XCTAssertEqual(m[a.allocation].unsignedIntValue(at: 0, ofType: .i(32)), 32)

    m[a.allocation].withUnsafeMutablePointer(to: UInt64.self, at: 0) { p in
      p.pointee = 64
    }
    XCTAssertEqual(m[a.allocation].unsignedIntValue(at: 0, ofType: .i(64)), 64)
  }

}

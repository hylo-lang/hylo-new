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

}

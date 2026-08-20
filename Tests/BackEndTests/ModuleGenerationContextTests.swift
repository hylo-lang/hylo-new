@testable import BackEnd
import Driver
import FrontEnd
import SwiftyLLVM
import XCTest

final class ModuleGenerationContextTests: XCTestCase {

  func testIntegerTypeToRepresent() throws {
    var driver = try Driver(targetSpecification: .native())
    let module = driver.program.demandModule("test")
    let m = ModuleGenerationContext(
      compiling: module, into: .init("test", targetMachine: .init(target: driver.target)))

    // A type representing `n` values must accommodate `0` through `n - 1`.
    XCTAssertEqual(m.integerTypeToRepresent(count: 0).unsafe[].bitWidth, 8)
    XCTAssertEqual(m.integerTypeToRepresent(count: 2).unsafe[].bitWidth, 8)
    XCTAssertEqual(m.integerTypeToRepresent(count: 0x100).unsafe[].bitWidth, 8)
    XCTAssertEqual(m.integerTypeToRepresent(count: 0x101).unsafe[].bitWidth, 16)
    XCTAssertEqual(m.integerTypeToRepresent(count: 0x10000).unsafe[].bitWidth, 16)
    XCTAssertEqual(m.integerTypeToRepresent(count: 0x10001).unsafe[].bitWidth, 32)
    XCTAssertEqual(m.integerTypeToRepresent(count: 0x1_0000_0000).unsafe[].bitWidth, 32)
    XCTAssertEqual(m.integerTypeToRepresent(count: 0x1_0000_0001).unsafe[].bitWidth, 64)
  }

}

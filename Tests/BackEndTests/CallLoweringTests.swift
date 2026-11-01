@testable import BackEnd
import Driver
import FrontEnd
import SwiftyLLVM
import XCTest

final class CallLoweringTests: XCTestCase {

  func testCallReturningByReference() async throws {
    var driver = try Driver(targetSpecification: .native())
    try await driver.loadStandardLibrary()

    let m = driver.program.demandModule("m0")
    driver.program[m].addDependency(Module.standardLibraryName)

    // A function whose result doesn't fit in a register.
    driver.program[m].addSource("public fun f() -> {Int, Int} { (1, 2) }")
    await driver.assignScopes(of: m)
    await driver.assignTypes(of: m)
    await driver.lower(m)
    XCTAssertFalse(driver.program[m].containsError)

    var ctx = ModuleGenerationContext(
      compiling: m, into: .init("m0", targetMachine: .init(target: driver.target)))
    let callee = driver.program.demandFunction(0, in: &ctx)
    let output = try XCTUnwrap(callee.prototype.mapping.output)
    XCTAssertEqual(output.convention, .byReference(0))

    // Return the result of `f` from another function, so that LLVM checks its type.
    let caller =
      ctx.llvm.declareFunction("g", ctx.llvm.functionType(from: [], to: output.type.llvm))
    let p = ctx.llvm.endOf(ctx.llvm.appendBlock(to: caller))
    let r = driver.program.insertCall(callee, with: [], at: p, in: caller, in: &ctx)
    ctx.llvm.insertReturn(r, at: p)
    let llvm = ctx.release()
    XCTAssertNoThrow(try llvm.verify())
  }

}

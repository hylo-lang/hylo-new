import BackEnd
import Driver
import FrontEnd
import XCTest

final class SimpleFunctionEmitterTest: XCTestCase {

  // TODO: Re-enable when transpileToLLVM is implemented.
  func testTrivial() async throws {
    var driver = try Driver(targetSpecification: .native())

    let m = driver.program.demandModule("M0")

    if await driver.assignScopes(of: m).containsError { return XCTFail("Failed to assign scopes") }
    if await driver.assignTypes(of: m).containsError { return XCTFail("Failed to assign types") }

    // IR Lowering.
    let l = await driver.lower(m)
    if l.containsError { return XCTFail("Failed to lower IR") }

    // IR Transformation passes.
    let t = await driver.applyTransformationPasses(m)
    if t.containsError { return XCTFail("Failed to apply transformation passes") }

    // LLVM Lowering.
    if (try driver.compileToLLVM(m)).containsError { return XCTFail("Failed to lower to LLVM") }

    XCTAssertEqual(
      driver.llvmIR(of: m),
      """
      ; ModuleID = 'MainModule'
      source_filename = "MainModule"

      define i32 @main() {
        ret i32 0
      }

      """)

    XCTAssertTrue(try driver.assembly(of: m).contains("main:"))

    let output = try FileManager.default.withUniqueTemporaryDirectory { (d) in
      let executable = d.appendingPathComponent(driver.program[m].name)
      _ = try driver.generateExecutable(from: m, writingTo: executable)
      return try Process.executionOutput(executable)
    }

    XCTAssertEqual(output.trimming(while: \.isWhitespace), "")
  }

}

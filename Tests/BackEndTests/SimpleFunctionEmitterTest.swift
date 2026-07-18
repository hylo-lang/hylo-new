import BackEnd
import Driver
import FrontEnd
import XCTest

final class SimpleFunctionEmitterTest: XCTestCase {

  func testTrivial() async throws {
    var driver = try Driver(targetSpecification: .native())

    let m = driver.program.demandModule("test")
    let s: SourceFile = "public fun main() {}"
    driver.program[m].addSource(s)

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
    let llvmIR = try XCTUnwrap(driver.llvmIR(of: m))

    // Did de lower the main function?
    XCTAssert(
      llvmIR.containsOnce(
        """
        define private void @"$hM6testvUpvirtualu6rky9fkv9x3F06mainlT01tR50tR5$gP71L1L1L"() {
          %1 = alloca {}, align 8
          ret void
        }
        """))

    // Did de lower the entry point?
    XCTAssert(
      llvmIR.containsOnce(
        """
        define i32 @main() {
          call void @"$hM6testvUpvirtualu6rky9fkv9x3F06mainlT01tR50tR5$gP71L1L1L"()
          ret i32 0
        }
        """))

    let output = try FileManager.default.withUniqueTemporaryDirectory { (d) in
      let executable = d.appendingPathComponent(driver.program[m].name)
      _ = try driver.generateExecutable(from: m, writingTo: executable)
      return try Process.executionOutput(executable)
    }

    XCTAssertEqual(output.trimming(while: \.isWhitespace), "")
  }

}

extension StringProtocol {

  /// Returns `true` iff `self` contains exactly one occurrence of `s`.s
  fileprivate func containsOnce(_ s: String) -> Bool {
    if let i = self.firstRange(of: s) {
      return !self.suffix(from: i.upperBound).contains(s)
    } else {
      return false
    }
  }

}

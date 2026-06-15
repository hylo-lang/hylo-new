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
        define private void @"M6testvUpvirtualu6rky9fkv9x3F06mainlT01tR50tR5$gP71L1L1L"() {
          %1 = alloca {}, align 8
          ret void
        }
        """))

    // Did de lower the entry point?
    XCTAssert(
      llvmIR.containsOnce(
        """
        define i32 @main() {
          call void @"M6testvUpvirtualu6rky9fkv9x3F06mainlT01tR50tR5$gP71L1L1L"()
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

  func testLoweringStdlib() async throws {

    var d = try Driver(targetSpecification: .native())
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule("M0")

    d.program[m0].addDependency(Module.standardLibraryName)

    _ = d.program[m0].addSource(
      """
      fun create() -> Int32 {
        Int32()
      }
      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)

    d.program.assignTypes(m0, loggingInferenceWhere: { (_, _) in false })
    try assertNoDiagnostics(in: d.program)

    d.program.lower(m0)
    d.program.lower(d.program.modules[Module.standardLibraryName]!.identity)

    let stdlib = d.program.modules[Module.standardLibraryName]!.identity
    print("STD LIB DIAGNOSTICS AFTER LOWERING: \(Array(d.program[stdlib].diagnostics).count)")
    for diag in d.program[stdlib].diagnostics {
      print("  - \(diag)")
    }
    print("ALL DIAGNOSTICS AFTER LOWERING: \(Array(d.program.diagnostics).count)")

    var p1 = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map { $0.show(using: &p1) }.joined(separator: "\n"),
      """
      fun create(set %p0: Int32) {
      %b0:
        %r0 = alloca Void, #preferred
        %r1 = access [set] %p0
        %r2 = access [set] %r0
        %r3 = apply Int32.init(%r1) => %r2
        %r4 = return
      }
      fun Int32.init(set %p0: Int32, set %p1: Void)
      """)

    try assertNoDiagnostics(in: d.program)

    d.program.applyTransformationPasses(m0)
    try assertNoDiagnostics(in: d.program)
    
    d.program.applyTransformationPasses(d.program.modules[Module.standardLibraryName]!.identity)
    try assertNoDiagnostics(in: d.program)

    _ = try d.compileToLLVM(m0)
    let llvmIR = try XCTUnwrap(d.llvmIR(of: m0))

    XCTAssertEqual(
      llvmIR,
      """
      ; ModuleID = 'M0'
      source_filename = "M0"

      %sTR0U7Int32S10 = type <{ i32 }>
      %tR5 = type <{}>

      define %sTR0U7Int32S10 @"M4M0vUpvirtual8edhh9xvl5n9F08createlT01tR50sTR0U7Int32S13$eP71L1L1L"() {
        %1 = alloca %tR5, align 1
        %2 = alloca %sTR0U7Int32S10, align 4
        call void @R0U7Int32S10F06initlT01tR516selfsTK1tR5(ptr %2)
        %3 = load %sTR0U7Int32S10, ptr %2, align 1
        ret %sTR0U7Int32S10 %3
      }

      declare void @R0U7Int32S10F06initlT01tR516selfsTK1tR5(ptr)
      """)
  }

}

/// Asserts that `program` has no diagnostics.
func assertNoDiagnostics(
  in program: Program, file: StaticString = #filePath, line: UInt = #line
) throws {
  if !program.diagnostics.isEmpty {
    XCTFail(
      """
      Expected no diagnostics, but found \(program.diagnostics.count):
      \(program.diagnostics.map { "\($0.level): \($0)" }.joined(separator: "\n"))
      """,
      file: file, line: line)

    throw CompilationError(diagnostics: program.diagnostics.map { $0 })
  }
}

/// An error reported on failed compilation.
struct CompilationError: Error {
  let diagnostics: [Diagnostic]
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

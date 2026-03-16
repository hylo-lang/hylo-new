import Driver
import FrontEnd
import LLVMEmitter
import XCTest

final class SimpleFunctionEmitterTest: XCTestCase {
  func testSimpleFunction() async throws {
    var d = Driver()
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule(.init("M0"))

    d.program[m0].addDependency(.standardLibrary)

    _ = d.program[m0].addSource(
      """
      fun add(x: Simplint, y: Simplint) -> Simplint {
        x + y
      }
      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.assignTypes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.lower(m0)

    
    var p1 = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map{ $0.show(using: &p1) }.joined(separator: "\n"),
      """
      fun add(_:_:)(let %p0: Simplint&, let %p1: Simplint&, set %p2: Simplint&) {
      %b0:
        %r0 = access [let] %p0
        %r1 = access [let] %p1
        %r2 = access [set] %p2
        %r3 = apply Simplint.infix+(%r0, %r1) => %r2
        %r4 = end %r2
        %r5 = end %r1
        %r6 = end %r0
        %r7 = return
      }
      fun Simplint.infix+(let %p0: Simplint&, let %p1: Simplint&, set %p2: Simplint&)
      """)

    try assertNoDiagnostics(in: d.program)
    d.program.applyTransformationPasses(m0)
    try assertNoDiagnostics(in: d.program)

    var p = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map{ $0.show(using: &p) }.joined(separator: "\n"),
      """
      fun add(_:_:)(let %p0: Simplint&, let %p1: Simplint&, set %p2: Simplint&) {
      %b0:
        %r0 = access [let] %p0
        %r1 = access [let] %p1
        %r2 = access [set] %p2
        %r3 = apply Simplint.infix+(%r0, %r1) => %r2
        %r4 = end %r2
        %r5 = end %r1
        %r6 = end %r0
        %r7 = return
      }
      fun Simplint.infix+(let %p0: Simplint&, let %p1: Simplint&, set %p2: Simplint&)
      """)

    let c = try CodeGenerationContext.transpiling(m0, in: d.program, compilingFor: .host())
    XCTAssertEqual(
      c.llvm.llCode(),
      """
      ; ModuleID = 'M0'
      source_filename = "M0"

      define void @"hylo_add(_:_:)"(ptr noalias nocapture nofree readonly %0, ptr noalias nocapture nofree readonly %1, ptr noalias nocapture nofree %2) {
      prologue:
        br label %b0

      b0:                                               ; preds = %prologue
        call void @"hylo_Simplint.infix+"(ptr %0, ptr %1, ptr %2)
        ret void
      }

      declare void @"hylo_Simplint.infix+"(ptr noalias nocapture nofree readonly, ptr noalias nocapture nofree readonly, ptr noalias nocapture nofree)

      """)

  }

   func testMain() async throws {
    var d = Driver()
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule(.init("M0"))

    d.program[m0].addDependency(.standardLibrary)

    _ = d.program[m0].addSource(
      """
      fun main() {
      
      }

      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.assignTypes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.lower(m0)

    
    try assertNoDiagnostics(in: d.program)
    d.program.applyTransformationPasses(m0)
    try assertNoDiagnostics(in: d.program)

    let c = try CodeGenerationContext.transpiling(m0, in: d.program, compilingFor: .host())
    XCTAssertEqual(
      c.llvm.llCode(),
      """
      ; ModuleID = 'M0'
      source_filename = "M0"

      define private void @hylo_main(ptr noalias nocapture nofree %0) {
      prologue:
        br label %b0

      b0:                                               ; preds = %prologue
        ret void
      }

      define i32 @main() {
        %1 = alloca {}, align 8
        call void @hylo_main(ptr %1)
        ret i32 0
      }

      """)

  }
}

func assertNoDiagnostics(in program: Program, file: StaticString = #file, line: UInt = #line) throws
{
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

struct CompilationError: Error {
  let diagnostics: [Diagnostic]
}

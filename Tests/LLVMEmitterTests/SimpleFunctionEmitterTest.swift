import Driver
import FrontEnd
import LLVMEmitter
import XCTest

final class SimpleFunctionEmitterTest: XCTestCase {
  func testInt32Addition() async throws {
    var d = Driver(moduleCachePath: nil, targetConfiguration: .init(), standardLibrary: .localMinimal())
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule(.init("M0"))

    d.program[m0].addDependency(Module.standardLibraryName)

    _ = d.program[m0].addSource(
      """
      fun add(x: Int, y: Int) -> Int {
        x + y
      }
      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.assignTypes(m0, loggingInferenceWhere: { _, _ in false })
    try assertNoDiagnostics(in: d.program)
    d.program.lower(m0)

    var p1 = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map { $0.show(using: &p1) }.joined(separator: "\n"),
      """
      fun add(_:_:)(let %p0: Int&, let %p1: Int&, set %p2: Int&) {
      %b0:
        %r0 = access [let] %p0
        %r1 = access [let] %p1
        %r2 = access [set] %p2
        %r3 = apply Int.infix+(%r0, %r1) => %r2
        %r4 = end %r2
        %r5 = end %r1
        %r6 = end %r0
        %r7 = return
      }
      fun Int.infix+(let %p0: Int&, let %p1: Int&, set %p2: Int&)
      """)

    try assertNoDiagnostics(in: d.program)
    d.program.applyTransformationPasses(m0)
    try assertNoDiagnostics(in: d.program)

    var p = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map { $0.show(using: &p) }.joined(separator: "\n"),
      """
      fun add(_:_:)(let %p0: Int&, let %p1: Int&, set %p2: Int&) {
      %b0:
        %r0 = access [let] %p0
        %r1 = access [let] %p1
        %r2 = access [set] %p2
        %r3 = apply Int.infix+(%r0, %r1) => %r2
        %r4 = end %r2
        %r5 = end %r1
        %r6 = end %r0
        %r7 = return
      }
      fun Int.infix+(let %p0: Int&, let %p1: Int&, set %p2: Int&)
      """)

    let m = try transpileToLLVM(m0, in: d.program, compilingFor: .host())
    XCTAssertEqual(
      m.llCode(),
      """
      ; ModuleID = 'M0'
      source_filename = "M0"

      define void @"hylo_add(_:_:)"(ptr noalias nocapture nofree readonly %0, ptr noalias nocapture nofree readonly %1, ptr noalias nocapture nofree %2) {
      prologue:
        br label %b0

      b0:                                               ; preds = %prologue
        call void @hylo_int_infix_add(ptr %0, ptr %1, ptr %2)
        ret void
      }

      declare void @hylo_int_infix_add(ptr noalias nocapture nofree readonly, ptr noalias nocapture nofree readonly, ptr noalias nocapture nofree)

      """)

  }
  func testInt32Creation() async throws {
    var d = Driver(moduleCachePath: nil, targetConfiguration: .init(), standardLibrary: .localMinimal())
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule(.init("M0"))

    d.program[m0].addDependency(Module.standardLibraryName)

    _ = d.program[m0].addSource(
      """
      fun create() -> Int32 {
        Int32()
      }
      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.assignTypes(m0, loggingInferenceWhere: { _, _ in false })
    try assertNoDiagnostics(in: d.program)
    d.program.lower(m0)
    // d.program.lower(d.program.modules[.standardLibrary]!.identity)

    var p1 = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map { $0.show(using: &p1) }.joined(separator: "\n"),
      """
      fun create(set %p0: Int32&) {
      %b0:
        %r0 = alloca Void, #preferred
        %r1 = access [set] %p0
        %r2 = access [set] %r0
        %r3 = apply Int32.init(%r1) => %r2
        %r4 = end %r2
        %r5 = end %r1
        %r6 = return
      }
      fun Int32.init(set %p0: Int32&, set %p1: Void&)
      """)

    try assertNoDiagnostics(in: d.program)
    d.program.applyTransformationPasses(m0)
    d.program.applyTransformationPasses(d.program.modules[Module.standardLibraryName]!.identity)

    try assertNoDiagnostics(in: d.program)

    var p = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map { $0.show(using: &p) }.joined(separator: "\n"),
      """
      fun create(set %p0: Int32&) {
      %b0:
        %r0 = alloca Void, #preferred
        %r1 = access [set] %p0
        %r2 = access [set] %r0
        %r3 = apply Int32.init(%r1) => %r2
        %r4 = end %r2
        %r5 = end %r1
        %r7 = access [sink] %r0
        %r8 = assume_state %r7 uninitialized
        %r9 = end %r7
        %r6 = return
      }
      fun Int32.init(set %p0: Int32&, set %p1: Void&)
      """)

    let m = try transpileToLLVM(m0, in: d.program, compilingFor: .host())
    XCTAssertEqual(
      m.llCode(),
      """
      ; ModuleID = 'M0'
      source_filename = "M0"

      define void @hylo_create(ptr noalias nocapture nofree %0) {
      prologue:
        br label %b0

      b0:                                               ; preds = %prologue
        call void @hylo_Int32.init(ptr %0, ptr null)
        ret void
      }

      declare void @hylo_Int32.init(ptr noalias nocapture nofree, ptr noalias nocapture nofree)

      """)

  }

  func testMain() async throws {
    var d = Driver()
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule(.init("M0"))

    d.program[m0].addDependency(Module.standardLibraryName)

    _ = d.program[m0].addSource(
      """
      fun main() {

      }

      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.assignTypes(m0, loggingInferenceWhere: { _, _ in false })
    try assertNoDiagnostics(in: d.program)
    d.program.lower(m0)

    try assertNoDiagnostics(in: d.program)
    d.program.applyTransformationPasses(m0)
    try assertNoDiagnostics(in: d.program)

    let m = try transpileToLLVM(m0, in: d.program, compilingFor: .host())
    XCTAssertEqual(
      m.llCode(),
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

  func stdlibLoweringCrashes() -> Bool {
    true
  }

  func testLoweringStdlib() async throws {
    if stdlibLoweringCrashes() {
      throw XCTSkip()
    }

    var d = Driver(moduleCachePath: nil)
    try await d.loadStandardLibrary()

    let m0 = d.program.demandModule(.init("M0"))

    d.program[m0].addDependency(Module.standardLibraryName)

    _ = d.program[m0].addSource(
      """
      fun create() -> Int32 {
        Int32()
      }
      """)

    await d.program.assignScopes(m0)
    try assertNoDiagnostics(in: d.program)
    d.program.assignTypes(m0, loggingInferenceWhere: { _, _ in false })
    try assertNoDiagnostics(in: d.program)
    d.program.lower(m0)
    d.program.lower(d.program.modules[Module.standardLibraryName]!.identity)

    var p1 = TreePrinter(program: d.program)
    XCTAssertEqual(
      d.program[m0].functions.map { $0.show(using: &p1) }.joined(separator: "\n"),
      """
      fun create(set %p0: Int32&) {
      %b0:
        %r0 = subfield %p0 at 0 as i32
        %r1 = access [set] %r0
        %r2 = store i32 42 to %r1
        %r3 = end %r1
        %r4 = return
      }
      """)

    try assertNoDiagnostics(in: d.program)
    d.program.applyTransformationPasses(m0)
    d.program.applyTransformationPasses(d.program.modules[Module.standardLibraryName]!.identity)

  }
}

/// Asserts that `program` has no diagnostics.
func assertNoDiagnostics(in program: Program, file: StaticString = #filePath, line: UInt = #line)
  throws
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

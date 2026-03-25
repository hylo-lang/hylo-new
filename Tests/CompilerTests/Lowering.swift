import Driver
import FrontEnd
import XCTest

final class LoweringTests: XCTestCase {
    func testLoweringStdlib() async throws {
        var d = Driver(moduleCachePath: nil)
        try await d.loadStandardLibrary()

        let m0 = d.program.demandModule(.init("M0"))

        d.program[m0].addDependency(Module.standardLibraryName)

        _ = d.program[m0].addSource(
            """
            fun create() -> Int {
              // 4  // FrontEnd/Program.swift:666: Fatal error: untyped node at /home/ambrus/hylo-new/triage-crash-hn2/StandardLibrary/Sources/Core/Numbers/AdditiveArithmetic.hylo:2.41-50
            
              // .zero()  // FrontEnd/IREmitter.swift:450: Fatal error: unexpected node 'ImplicitQualification' at virtual://1rq7u984nxlse:4.3-4

              Int() // FrontEnd/Program.swift:666: Fatal error: untyped node at /home/ambrus/hylo-new/triage-crash-hn2/StandardLibrary/Sources/Core/Numbers/AdditiveArithmetic.hylo:2.41-50

            }

            """)

        await d.program.assignScopes(m0)
        try assertNoDiagnostics(in: d.program)
        d.program.assignTypes(m0, loggingInferenceWhere: {_, _ in false})
        try assertNoDiagnostics(in: d.program)
        d.program.lower(m0)
        d.program.lower(d.program.modules[Module.standardLibraryName]!.identity)

        var p1 = TreePrinter(program: d.program)
        XCTAssertEqual(
            d.program[m0].functions.map { $0.show(using: &p1) }.joined(separator: "\n"),
            """
            let's see
            """)

        try assertNoDiagnostics(in: d.program)
        d.program.applyTransformationPasses(m0)
        d.program.applyTransformationPasses(d.program.modules[Module.standardLibraryName]!.identity)

    }
}
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

import FrontEnd
import Interpreter
import XCTest

final class InterpreterRunTests: XCTestCase {

  func testPositiveTestProgramsRun() async throws {
    let u = Bundle.module.url(
      forResource: "InterpreterTestPrograms/PositiveTests", withExtension: nil)!
    let fs = try FileManager.default.contentsOfDirectory(
      at: u,
      includingPropertiesForKeys: nil
    )
    for f in fs {
      print(f)  // TODO: kept for debugging and observability.
      let p = try await Program.loadForInterpretation(sourceRoot: f)
      try p.interpret()
      print()
    }
  }

  func testBuiltinTrap() async throws {
    await check(throws: Interpreter.Trap()) {
      try await interpretProgram(at: "InterpreterTestPrograms/NegativeTests/AlwaysTrap.hylo")
    }
  }

  /// Loads and interprets the program at the resource path `location`,
  /// relative to the module's resource bundle.
  private func interpretProgram(at location: String) async throws {
    let f = Bundle.module.url(forResource: location, withExtension: nil)!
    print(f)  // TODO: kept for debugging and observability.
    let p = try await Program.loadForInterpretation(sourceRoot: f)
    try p.interpret()
    print()
  }

}

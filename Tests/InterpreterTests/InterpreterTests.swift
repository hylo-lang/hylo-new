import XCTest
import FrontEnd

final class InterpreterRunTests: XCTestCase {

  func testProgramRuns() async throws {
    let u = Bundle.module.url(forResource: "InterpreterTestPrograms", withExtension: nil)!
    let fs = try FileManager.default.contentsOfDirectory(
      at: u,
      includingPropertiesForKeys: nil
    )
    for f in fs {
      let p = try await Program.loadForInterpretation(sourceRoot: f)
      try p.interpret()
    }
  }

}

import XCTest

final class InterpreterRunTests: XCTestCase {

  func testProgramRuns() async throws {
    let u = Bundle.module.url(forResource: "InterpreterTestPrograms", withExtension: nil)!
    let fs = try FileManager.default.contentsOfDirectory(
      at: u,
      includingPropertiesForKeys: nil
    )
    for f in fs {
      do {
        try await f.interpret()
      } catch {
        XCTFail(error.localizedDescription)
      }
    }
  }

}

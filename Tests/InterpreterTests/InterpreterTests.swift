import XCTest

final class InterpreterRunTests: XCTestCase {

  func testEmptyProgram() async throws {
    let s =
      """
        public fun main() { }
      """.sourceFile
    try await runOnInterpreter(s)
  }

}

import Driver
import Foundation
import FrontEnd
import Interpreter

extension Program {

  /// Returns the sources rooted at `r`, lowered for interpretation.
  static func loadForInterpretation(sourceRoot r: URL) async throws -> Program {
    var d = Driver(targetSpecification: try .host())
    try await d.loadStandardLibrary()
    try await d.load("Main", withSourcesAt: r)
    return d.program
  }

}

extension Program {

  /// Executes `self` on `Interpreter`.
  func interpret() throws {
    var executor = Interpreter(self)
    while executor.isRunning {
      // TODO: Kept for debugging and observability; remove when no longer needed.
      print(show(executor.currentInstruction))
      try executor.step()
    }
  }

}

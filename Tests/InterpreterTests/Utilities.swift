import Driver
import Foundation
import FrontEnd
import Interpreter

extension Program {

  /// Returns a program loaded from `u` and lowered for interpretation.
  static func loadForInterpretation(from u: URL) async throws -> Program {
    var d = Driver(targetSpecification: try .host())
    try await d.loadStandardLibrary()
    try await d.load("Main", withSourcesAt: u, dependingOnStandardLibrary: true)
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

extension Driver {

  /// Loads `m` from `root`, making it depend on the standard library if
  /// `dependingOnStandardLibrary` is `true`.
  fileprivate mutating func load(
    _ m: Module.Name,
    withSourcesAt root: URL,
    dependingOnStandardLibrary: Bool
  ) async throws {
    if dependingOnStandardLibrary {
      let r = program.demandModule(m)
      program[r].addDependency(Module.standardLibraryName)
    }
    try await load(m, withSourcesAt: root)
  }

}

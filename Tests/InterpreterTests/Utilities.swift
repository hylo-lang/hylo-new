import Foundation
import FrontEnd
import Interpreter
import Driver

/// Execute `p` on interpreter.
private func execute(_ p: Program) throws {
  var executor = Interpreter(p)
  while executor.isRunning {
    // TODO: Kept for debugging and observability; remove when no longer needed.
    print(p.show(executor.currentInstruction))
    try executor.step()
  }
}

extension URL {

  /// Runs program at `self` on `Interpreter`.
  func interpret() async throws {
    var d = Driver(targetSpecification: try .host())
    try await d.loadStandardLibrary()
    try await d.load("Main", withSourcesAt: self, dependingOnStandardLibrary: true)
    try execute(d.program)
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


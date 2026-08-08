import Driver
import Foundation
import FrontEnd
import Interpreter
import XCTest

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

  /// Returns the type erased identity of `t`.
  mutating func id<T: TypeTree>(_ t: T) -> AnyTypeIdentity {
    types.demand(t).erased
  }
}

/// Executes `action` and reports test failure if it does not throw `error`.
public func check<E: Error & Equatable, R>(
  throws expectedError: E, _ action: () throws -> R, file: StaticString = #filePath,
  line: UInt = #line
) {
  XCTAssertThrowsError(try action(), file: file, line: line) {
    XCTAssertEqual($0 as? E, expectedError, "\($0)", file: file, line: line)
  }
}

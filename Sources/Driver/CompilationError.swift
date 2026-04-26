import FrontEnd

/// An error that occurred during compilation.
public struct CompilationError: Error, CustomStringConvertible {

  /// The diagnostics of the error.
  public let diagnostics: DiagnosticSet

  public var description: String {
    diagnostics.elements.joinedString(separator: "\n", transform: { d in d.description })
  }

}

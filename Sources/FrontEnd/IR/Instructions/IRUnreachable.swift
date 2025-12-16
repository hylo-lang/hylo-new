import Archivist

/// Marks the execution path as unreachable.
public struct IRUnreachable: Terminator {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

}

extension IRUnreachable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "unreachable"
  }

}

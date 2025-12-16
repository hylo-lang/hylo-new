import Archivist

/// Returns control flow to the caller.
///
/// This instruction is only about control flow. Return values are stored in the return registers
/// before control flow leaves the function.
///
/// Refined IR requires that the return register of the function be definitely initialized before
/// `return` is executed.
public struct IRReturn: Terminator {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

}

extension IRReturn: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "return"
  }

}

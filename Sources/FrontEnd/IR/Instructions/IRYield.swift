/// Projects a value out of the current function.
///
/// This instruction is only about control flow. Return values are stored in the return registers
/// before control flow leaves the function.
///
/// Refined IR requires that the return register of the function be definitely initialized before
/// `return` is executed.
public struct IRYield: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(projectee: IRValue, anchor: Anchor) {
    self.operands = [projectee]
    self.anchor = anchor
  }

  /// The value being projected.
  public var projectee: IRValue {
    operands[0]
  }

}

extension IRYield: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "yield \(printer.show(projectee))"
  }

}

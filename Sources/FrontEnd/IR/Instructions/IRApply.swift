import Utilities

/// Invokes an IR function.
///
/// This instruction does not define any register. The return value of the function being applied
/// is stored in the last argument of the function, which is always a `set` access.
public struct IRApply: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(
    callee: IRValue,
    arguments: [IRValue],
    result: IRValue,
    anchor: Anchor
  ) {
    var operands = Array<IRValue>(minimumCapacity: arguments.count + 2)
    operands.append(callee)
    operands.append(contentsOf: arguments)
    operands.append(result)

    self.operands = operands
    self.anchor = anchor
  }

  /// The function being applied.
  public var callee: IRValue {
    operands[0]
  }

  /// The arguments of the call (excluding the return register).
  public var arguments: ArraySlice<IRValue> {
    operands.dropFirst().dropLast()
  }

  /// The register in which the result of the function is stored.
  public var result: IRValue {
    operands.last!
  }

}

extension IRApply: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "apply \(printer.show(callee))(\(printer.show(arguments))) => \(printer.show(result))"
  }

}

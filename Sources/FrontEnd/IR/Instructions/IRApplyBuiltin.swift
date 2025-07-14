/// Invokes a function of the `Builtin` module.
public struct IRApplyBuiltin: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The function being called.
  public let callee: BuiltinFunction

  /// The type of the value returned by `callee`.
  public let returnTypeOfCallee: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    callee: BuiltinFunction,
    returnTypeOfCallee: AnyTypeIdentity,
    arguments: [IRValue],
    anchor: Anchor
  ) {
    self.operands = arguments
    self.anchor = anchor
    self.callee = callee
    self.returnTypeOfCallee = returnTypeOfCallee
  }

  /// The arguments of the call.
  public var arguments: [IRValue] {
    operands
  }

  /// The type of the value returned by `callee`.
  public var type: IRType {
    .addressOf(returnTypeOfCallee)
  }

}

extension IRApplyBuiltin: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "apply_builtin \(printer.show(callee))(\(printer.show(arguments)))"
  }

}

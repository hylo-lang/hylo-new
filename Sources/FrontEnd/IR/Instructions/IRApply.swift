/// Invokes an IR function.
public struct IRApply: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type arguments of passed to the function.
  public let typeArguments: TypeArguments

  /// Creates an instance with the given properties.
  public init(
    callee: IRValue,
    typeArguments: TypeArguments,
    termArguments: [IRValue],
    anchor: Anchor
  ) {
    self.operands = Array(callee, prependedTo: termArguments)
    self.anchor = anchor
    self.typeArguments = typeArguments
  }

  /// The function being called.
  public var callee: IRValue {
    operands[0]
  }

  /// The arguments of the call.
  public var termArguments: ArraySlice<IRValue> {
    operands[1...]
  }

}

extension IRApply: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = "apply \(printer.show(callee))"
    if !typeArguments.isEmpty {
      result.append("<\(printer.show(typeArguments.values))>")
    }
    result.append("(\(printer.show(termArguments)))")
    return result
  }

}

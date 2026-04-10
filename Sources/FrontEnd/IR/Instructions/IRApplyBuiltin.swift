/// Invokes a function of the `Builtin` module.
///
/// Unlike `apply`, this instruction does produce a result.
public struct IRApplyBuiltin: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The function being applied.
  public let callee: BuiltinFunction

  /// The type of the value returned by `callee`.
  public let type: IRType

  /// Creates an instance with the given properties.
  public init(
    callee: BuiltinFunction, returnTypeOfCallee: AnyTypeIdentity, arguments: [IRValue],
    anchor: Anchor
  ) {
    self.operands = arguments
    self.anchor = anchor
    self.callee = callee
    self.type = .value(returnTypeOfCallee)
  }

  /// Creates a copy of `other`, substituting its properities with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in ss[o] })
    self.anchor = other.anchor
    self.callee = other.callee
    self.type = other.type
  }

  /// The arguments of the call.
  public var arguments: [IRValue] {
    operands
  }

}

extension IRApplyBuiltin: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "apply_builtin \(printer.show(callee))(\(printer.show(arguments)))"
  }

}

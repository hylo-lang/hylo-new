import Archivist

/// Invokes a function of the `Builtin` module.
///
///     apply_builtin <callee : builtin-function>(<v0 : value>, ..., <vn : value>)
///
/// `apply_builtin` applies the built-in function `callee` on arguments `v0` to `vn`, defining a
/// register with the result of the application. Note that this behavior is unlike `apply`, which
/// writes its result to a `set` parameter.
@Archivable
public struct IRApplyBuiltin: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The function being applied.
  public let callee: BuiltinFunction

  /// The capabilities taken by the callee's parameters.
  public let inputs: [AccessEffect]

  /// The return type of the callee.
  public let output: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    callee: BuiltinFunction, inputs: [AccessEffect], output: AnyTypeIdentity, arguments: [IRValue],
    anchor: Anchor
  ) {
    self.operands = arguments
    self.anchor = anchor
    self.callee = callee
    self.inputs = inputs
    self.output = output
  }

  /// Creates a copy of `other`, substituting its properties with `properties`.
  public init(_ other: Self, substituting properties: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in properties[o] })
    self.anchor = properties.anchor(other)
    self.callee = other.callee
    self.inputs = other.inputs
    self.output = other.output
  }

  /// The arguments of the call.
  public var arguments: [IRValue] {
    operands
  }

  /// The type of the storage accessed by this instruction.
  public var type: IRType {
    .value(output)
  }

}

extension IRApplyBuiltin: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "apply_builtin \(printer.show(callee))(\(printer.show(arguments)))"
  }

}

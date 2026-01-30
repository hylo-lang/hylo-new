import Utilities

/// Applies a type abstraction.
///
/// This instruction is used to supplies type arguments to polymorphic values.
public struct IRTypeApply: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type arguments of passed to the function.
  public let arguments: TypeArguments

  /// The result of applying the abstraction's type to `typeArguments`.
  public let typeOfApplication: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    callee: IRValue,
    arguments: TypeArguments,
    typeOfApplication: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = [callee]
    self.anchor = anchor
    self.arguments = arguments
    self.typeOfApplication = typeOfApplication
  }

  /// The type abstraction being applied.
  public var callee: IRValue {
    operands[0]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .lowered(typeOfApplication, isAddress: true)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

  /// Asserts that the well-formedness conditions of the instruction hold.
  public func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool {
    // The callee must be instance of a universal type.
    guard
      let t = parent.result(of: callee),
      let u = program.types.cast(t.type, to: UniversalType.self)
    else { preconditionFailure("monomorphic callee") }

    // The callee must have an address type.
    precondition(t.isAddress, "callee must have an address type")

    // The type arguments must match the callee's parameters.
    precondition(
      program.types[u].parameters.elementsEqual(arguments.elements.keys),
      "type arguments do not match type parameters")
    precondition(
      typeOfApplication == program.types.substitute(arguments, in: .init(u)),
      "invalid result type")

    return true
  }

}

extension IRTypeApply: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "type_apply \(printer.show(callee))<\(printer.show(arguments.values))>"
  }

}

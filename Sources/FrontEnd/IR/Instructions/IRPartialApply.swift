/// Creates a closure by partially applying a function to a sequence of arguments.
///
/// The function being partially applied is monomorphic (i.e., it does not accept any generic type
/// parameter). The sequence of arguments are passed to the parameters of the function, from left
/// to right. The lifetime of each argument is extended by the lifetime of the resulting closure.
public struct IRPartialApply: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the property being accessed.
  public let closureType: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    callee: IRValue, arguments: [IRValue], closureType: AnyTypeIdentity,
    anchor: Anchor
  ) {
    self.operands = Array(callee, prependedTo: arguments)
    self.anchor = anchor
    self.closureType = closureType
  }

  /// Creates a copy of `other`, substituting its properities with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in ss[o] })
    self.anchor = other.anchor
    self.closureType = other.closureType
  }

  /// The function being partially applied.
  public var callee: IRValue {
    operands[0]
  }

  /// The arguments of the call (excluding the return register).
  public var arguments: ArraySlice<IRValue> {
    operands[1...]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(closureType)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

}

extension IRPartialApply: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "partial_apply \(printer.show(callee))(\(printer.show(arguments)))"
  }

}

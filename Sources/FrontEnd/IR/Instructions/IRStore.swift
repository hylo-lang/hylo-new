/// Writes a value to memory.
///
/// The target refers to storage capable of holding the value being stored.
/// 
/// If the source is not a machine type, the operation requires exclusive access to the target,
/// which must be uninitialized before the operation. If the value to write is held in a register,
/// it is consumed and the register can no longer be used after the operation.
/// 
/// For machine types, we always copy the values, so no consume semantics.
/// 
/// Regardless of the type being stored, the target is in an initialized state after the operation.
public struct IRStore: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(value: IRValue, target: IRValue, anchor: Anchor) {
    self.operands = [value, target]
    self.anchor = anchor
  }

  /// The value to write.
  public var value: IRValue {
    operands[0]
  }

  /// The address of the storage to which the value is written.
  public var target: IRValue {
    operands[1]
  }

}

extension IRStore: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "store \(printer.show(value)) to \(printer.show(target))"
  }

}

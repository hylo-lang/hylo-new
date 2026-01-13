/// Copies the memory representation of the value stored in memory.
///
/// This instruction implements the behavior of `memcpy` from libc. The source of the copy must not
/// overlap with its destination.
public struct IRMemoryCopy: Instruction {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// Creates an instance with the given properties.
  public init(source: IRValue, target: IRValue, anchor: Anchor) {
    self.operands = [source, target]
    self.anchor = anchor
  }

  /// The address of the storage from which the value is read.
  public var source: IRValue {
    operands[0]
  }

  /// The address of the storage from which the value is written.
  public var target: IRValue {
    operands[1]
  }

}

extension IRMemoryCopy: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "memcpy \(printer.show(source)) to \(printer.show(target))"
  }

}

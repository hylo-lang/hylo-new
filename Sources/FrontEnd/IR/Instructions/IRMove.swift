/// Relocates a value to different storages.
///
/// This instruction abstracts over either move-assignment or move-initialization, depending on the
/// initialization state of the target. It is desugared to during lifetime normalization state and
/// does not occur in refined IR.
///
/// The target refers to storage capable of holding an the value held in the source. The operation
/// requires exclusive access on both the source and the target. The source must be initialized
/// before the operation and is left uninitialized after. The target is contains the value that
/// was held in the source after the operation.
public struct IRMove: Instruction {

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

extension IRMove: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "move \(printer.show(source)) to \(printer.show(target))"
  }

}

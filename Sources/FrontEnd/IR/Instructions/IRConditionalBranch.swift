import Archivist

/// Transfers control flow to the start one of two basic blocks.
public struct IRConditionalBranch: Terminator {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The basic blocks to which control flow may be transferred.
  public private(set) var successors: [IRBlock.ID]

  /// Creates an instance with the given properties.
  public init(condition: IRValue, onSuccess: IRBlock.ID, onFailure: IRBlock.ID, anchor: Anchor) {
    self.operands = [condition]
    self.anchor = anchor
    self.successors = [onSuccess, onFailure]
  }

  /// A Boolean condition determining where control flow will be transferred.
  public var condition: IRValue {
    operands[0]
  }

  /// The target of the branch if `condition` is true.
  public var onSuccess: IRBlock.ID {
    successors[0]
  }

  /// The target of the branch if `condition` is false.
  public var onFailure: IRBlock.ID {
    successors[1]
  }

  /// Replaces `old` with `new` and returns `true` iff `old` is successor of `self`.
  @discardableResult
  public mutating func replaceSuccessor(_ old: IRBlock.ID, with new: IRBlock.ID) -> Bool {
    var replaced = false
    for i in successors.indices where successors[i] == old {
      successors[i] = new
      replaced = true
    }
    return replaced
  }

}

extension IRConditionalBranch: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "condbr \(printer.show(condition)), %b\(onSuccess.rawValue), %b\(onFailure.rawValue)"
  }

}

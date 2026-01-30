import Archivist

/// Unconditionally transfers control flow to the start of a basic block.
public struct IRBranch: Terminator {

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The basic blocks to which control flow may be transferred.
  public private(set) var successors: [IRBlock.ID]

  /// Creates an instance with the given properties.
  public init(target: IRBlock.ID, anchor: Anchor) {
    self.anchor = anchor
    self.successors = [target]
  }

  /// The target of the branch.
  public var target: IRBlock.ID {
    successors[0]
  }

  /// Replaces `old` with `new` and returns `true` iff `old` is successor of `self`.
  @discardableResult
  public mutating func replaceSuccessor(_ old: IRBlock.ID, with new: IRBlock.ID) -> Bool {
    if successors[0] == old {
      successors[0] = new
      return true
    } else {
      return false
    }
  }

}

extension IRBranch: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "br %b\(target.rawValue)"
  }

}

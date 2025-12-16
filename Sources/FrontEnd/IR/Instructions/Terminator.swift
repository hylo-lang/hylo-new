/// An instruction that causes control flow to transfer.
public protocol Terminator: Instruction {

  /// The basic blocks to which control flow may transfer.
  var successors: [IRBlock.ID] { get }

  /// Replaces `old` with `new` and returns `true` iff `old` is successor of `self`.
  @discardableResult
  mutating func replaceSuccessor(_ old: IRBlock.ID, with new: IRBlock.ID) -> Bool

}

extension Terminator {

  public var successors: [IRBlock.ID] {
    []
  }

  public mutating func replaceSuccessor(_ old: IRBlock.ID, with new: IRBlock.ID) -> Bool {
    false
  }

}

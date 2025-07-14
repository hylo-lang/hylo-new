/// An instruction that causes control flow to transfer.
public protocol Terminator: Instruction {

  /// The basic blocks to which control flow may transfer.
  var successors: [Block.ID] { get }

  /// Replaces `old` with `new` and returns `true` iff `old` is successor of `self`.
  @discardableResult
  mutating func replaceSuccessor(_ old: Block.ID, with new: Block.ID) -> Bool

}

extension Terminator {

  public var successors: [Block.ID] {
    []
  }

}

/// Where an instruction should be inserted in a basic block.
internal enum InsertionPoint {

  /// Before another instruction.
  case before(AnyInstructionIdentity)

  /// The end of a basic block.
  case end(of: IRBlock.ID)

  /// Returns the insertion at the start of `b`, which is in `f`.
  static func start(of b: IRBlock.ID, in f: IRFunction) -> InsertionPoint {
    if let i = f.blocks[b].first, let j = f.instruction(after: i) {
      return .before(j)
    } else {
      return .end(of: b)
    }
  }

}

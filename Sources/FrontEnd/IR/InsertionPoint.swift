/// Where an instruction should be inserted in a basic block.
internal enum InsertionPoint {

  /// Before another instruction.
  case before(AnyInstructionIdentity)

  /// The start of a basic block.
  case start(of: IRBlock.ID)

  /// The end of a basic block.
  case end(of: IRBlock.ID)

}

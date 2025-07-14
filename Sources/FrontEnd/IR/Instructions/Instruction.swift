/// An instruction in Hylo IR.
public protocol Instruction: Hashable, Showable, Sendable {

  /// The operands of the instruction.
  var operands: [IRValue] { get }

  /// The type of the instruction's result.
  var type: IRType { get }

  /// The region of the code corresponding to this instruction.
  var anchor: Anchor { get }

}

extension Instruction {

  /// `true` iff `self` is a terminator instruction.
  public var isTerminator: Bool {
    self is any Terminator
  }

  public var operands: [IRValue] {
    []
  }

  public var type: IRType {
    .nothing
  }

}

/// An instruction in Hylo IR.
public protocol Instruction: Hashable, Showable, Sendable {

  /// The operands of the instruction.
  var operands: [IRValue] { get }

  /// The type of the instruction's result.
  var type: IRType { get }

  /// The region of the code corresponding to this instruction.
  var anchor: Anchor { get }

  /// `true` iff `self` extends the lifetime of its operands.
  var isExtendingOperandLifetimes: Bool { get }

  /// Creates a copy of `other`, substituting its properities with `ss`.
  init(_ other: Self, substituting ss: IRSubstitutionTable)

  /// Asserts that the well-formedness conditions of the instruction hold.
  func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool

}

extension Instruction {

  /// The identity of an instance of `Self`.
  public typealias ID = ConcreteInstructionIdentity<Self>

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

  public var isExtendingOperandLifetimes: Bool {
    false
  }

  /// Returns `self` in which properties have been replaced with their substitution in `ss`.
  public func substituting(_ ss: IRSubstitutionTable) -> Self {
    .init(self, substituting: ss)
  }

  public func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool {
    true
  }

}

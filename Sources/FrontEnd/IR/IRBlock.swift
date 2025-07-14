import StableCollections

/// A basic block in a Hylo IR function.
public struct IRBlock: Sendable {

  /// The identity of a basic block in an IR function.
  public typealias ID = List<IRBlock>.Address

  /// The first instruction in `self`, if any.
  public private(set) var first: AnyInstructionIdentity?

  /// The last instruction in `self`, if any.
  public private(set) var last: AnyInstructionIdentity?

  /// Creates an empty block in the given scope.
  public init() {
    self.first = nil
    self.last = nil
  }

  /// Assigns the first instruction of `self`.
  internal mutating func setFirst(_ i: AnyInstructionIdentity) {
    first = i
    if last == nil { last = i }
  }

  /// Assigns the last instruction of `self`.
  internal mutating func setLast(_ i: AnyInstructionIdentity) {
    last = i
    if first == nil { first = i }
  }

}

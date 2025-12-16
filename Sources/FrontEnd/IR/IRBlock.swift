import StableCollections

/// A basic block in a Hylo IR function.
///
/// This data structure is essentially a pair of positions into some containing IR function. The
/// components of this pair satisfy the following invariants:
///
/// * `first` is `nil` iff `last` is `nil`.
/// * If assigned, `first` is ordered before `last`.
///
/// These invariants are maintained by the containing IR function.
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

  /// `true` iff `self` contains no instruction.
  public var isEmpty: Bool {
    first == nil
  }

  /// Assigns the first instruction of `self`.
  ///
  /// Do not call this method directly. The contents of a basic block can only be modified through
  /// the API of the containing `IRFunction`.
  internal mutating func setFirst(_ i: AnyInstructionIdentity) {
    first = i
    if last == nil { last = i }
  }

  /// Assigns the last instruction of `self`.
  ///
  /// Do not call this method directly. The contents of a basic block can only be modified through
  /// the API of the containing `IRFunction`.
  internal mutating func setLast(_ i: AnyInstructionIdentity) {
    last = i
    if first == nil { first = i }
  }

}

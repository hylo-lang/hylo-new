import StableCollections

/// A type denoting the identity of an instruction.
public protocol InstructionIdentity: Comparable, Hashable, Sendable {

  /// The type-erased value of this identity.
  var erased: AnyInstructionIdentity { get }

  /// Creates an identifying the same node as `erased`.
  init(uncheckedFrom erased: AnyInstructionIdentity)

}

extension InstructionIdentity {

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func == <T: InstructionIdentity>(l: Self, r: T) -> Bool {
    l.erased == r.erased
  }

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func ~= <T: InstructionIdentity>(l: Self, r: T) -> Bool {
    l.erased == r.erased
  }

  /// Returns `true` if `l` is ordered before `r`.
  public static func < (l: Self, r: Self) -> Bool {
    l.erased < r.erased
  }

}

public struct AnyInstructionIdentity {

  /// The address of the instruction identified by `self` in its containing function.
  public let address: List<IRFunction.Slot>.Address

}

extension AnyInstructionIdentity: InstructionIdentity {

  /// Creates an identifying the same instruction as `erased`.
  public init(uncheckedFrom erased: AnyInstructionIdentity) {
    self = erased
  }

  /// The type-erased value of this identity.
  public var erased: AnyInstructionIdentity {
    self
  }

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func == <T: InstructionIdentity>(l: Self, r: T) -> Bool {
    l.address == r.erased.address
  }

  /// Returns `true` if `l` is ordered before `r`.
  public static func < (l: Self, r: Self) -> Bool {
    l.address < r.address
  }

}

/// The identity of a node in an abstract syntax tree.
public struct ConcreteInstructionIdentity<T: Instruction>: InstructionIdentity {

  /// The type-erased value of this identity.
  public let erased: AnyInstructionIdentity

  /// Creates an identifying the same node as `erased`.
  public init(uncheckedFrom erased: AnyInstructionIdentity) {
    self.erased = erased
  }

}

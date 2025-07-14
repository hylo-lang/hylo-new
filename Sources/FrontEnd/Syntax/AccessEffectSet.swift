import Archivist
import Utilities

/// A set of access effects.
@Archivable
public struct AccessEffectSet: Hashable, Sendable {

  /// The raw value of this set.
  public private(set) var rawValue: UInt8

  /// Creates an empty set.
  public init() {
    self.rawValue = 0
  }

  /// Creates an instance from its raw value.
  public init(rawValue: UInt8) {
    self.rawValue = rawValue
  }

  /// Creates an instance containing `k`.
  public init(_ k: AccessEffect) {
    self.rawValue = k.rawValue
  }

  /// `true` iff `self` contains no effect.
  public var isEmpty: Bool {
    rawValue == 0
  }

  /// A set with all access effects but `auto`.
  public static let all: Self = [.let, .set, .inout, .sink]

  /// A set with `.inout` and `.set`.
  public static let inplace: Self = [.inout, .set]

  /// A set with `.let` and `.sink`.
  public static let functional: Self = [.let, .sink]

}

extension AccessEffectSet: OptionSet {

  public typealias RawValue = UInt8

  public typealias Element = AccessEffect

  public func contains(_ member: AccessEffect) -> Bool {
    (rawValue & member.rawValue) == member.rawValue
  }

  @discardableResult
  public mutating func insert(
    _ newMember: AccessEffect
  ) -> (inserted: Bool, memberAfterInsert: AccessEffect) {
    if contains(newMember) {
      return (inserted: false, memberAfterInsert: newMember)
    } else {
      rawValue |= newMember.rawValue
      return (inserted: true, memberAfterInsert: newMember)
    }
  }

  @discardableResult
  public mutating func remove(_ member: AccessEffect) -> AccessEffect? {
    if contains(member) {
      rawValue &= ~member.rawValue
      return member
    } else {
      return nil
    }
  }

  @discardableResult
  public mutating func update(with newMember: AccessEffect) -> AccessEffect? {
    let (i, k) = insert(newMember)
    return i ? nil : k
  }

}

extension AccessEffectSet: Collection {

  public typealias Index = UInt8

  public var startIndex: UInt8 {
    self.isEmpty ? endIndex : (rawValue & (~rawValue + 1))
  }

  public var endIndex: UInt8 {
    1 << 7
  }

  public func index(after position: UInt8) -> UInt8 {
    var next = position
    repeat {
      next = next << 1
    } while (next != endIndex) && ((next & rawValue) != next)
    return next
  }

  public subscript(position: UInt8) -> AccessEffect {
    AccessEffect(rawValue: position)!
  }

}

extension AccessEffectSet: CustomStringConvertible {

  public var description: String {
    "[\(list: self)]"
  }

}

import BitCollections
import StableCollections

/// A set of basic block identities.
public struct IRBlockSet: Hashable, Sendable {

  /// The raw values of the identities in `self`.
  private(set) var rawValue: BitSet

  /// Creates an empty instance.
  public init() {
    self.rawValue = .init()
  }

  /// The elements in `self`.
  public var elements: some Sequence<IRBlock.ID> {
    rawValue.lazy.compactMap(IRBlock.ID.init(_:))
  }

  /// Inserts all the contents `other` into `self`.
  public mutating func formUnion<S: Sequence<IRBlock.ID>>(_ other: S) {
    for b in other { rawValue.insert(b.rawValue) }
  }

  /// Removes all elements in `self`.
  public mutating func removeAll() {
    self.rawValue = .init()
  }

}

extension IRBlockSet: SetAlgebra {

  public typealias Element = IRBlock.ID

  public func contains(_ b: IRBlock.ID) -> Bool {
    rawValue.contains(b.rawValue)
  }

  @discardableResult
  public mutating func insert(_ b: IRBlock.ID) -> (inserted: Bool, memberAfterInsert: IRBlock.ID) {
    let inserted = rawValue.insert(b.rawValue).inserted
    return (inserted, b)
  }

  @discardableResult
  public mutating func update(with b: IRBlock.ID) -> IRBlock.ID? {
    let inserted = rawValue.insert(b.rawValue).inserted
    return inserted ? b : nil
  }

  @discardableResult
  public mutating func remove(_ b: IRBlock.ID) -> IRBlock.ID? {
    rawValue.remove(b.rawValue).map({ _ in b })
  }

  public mutating func formUnion(_ other: Self) {
    rawValue.formUnion(other.rawValue)
  }

  public func union(_ other: IRBlockSet) -> IRBlockSet {
    var result = self
    result.formUnion(other)
    return result
  }

  public mutating func formIntersection(_ other: Self) {
    rawValue.formIntersection(other.rawValue)
  }

  public func intersection(_ other: IRBlockSet) -> IRBlockSet {
    var result = self
    result.formIntersection(other)
    return result
  }

  public mutating func formSymmetricDifference(_ other: Self) {
    rawValue.formSymmetricDifference(other.rawValue)
  }

  public func symmetricDifference(_ other: IRBlockSet) -> IRBlockSet {
    var result = self
    result.formSymmetricDifference(other)
    return result
  }

}

import BitCollections
import StableCollections

/// A set of basic block identities.
public struct IRBlockSet: Hashable, Sendable {

  /// The raw values of the identities in `self`.
  ///
  /// The elements of this collection can be passed to `IRFunction.decode(_:)` to obtain the
  /// corresponding identity.
  public private(set) var elements: BitSet

  /// Creates an empty instance.
  public init() {
    self.elements = .init()
  }

}

extension IRBlockSet: SetAlgebra {

  public typealias Element = IRBlock.ID

  public func contains(_ b: IRBlock.ID) -> Bool {
    elements.contains(b.rawValue)
  }

  @discardableResult
  public mutating func insert(_ b: IRBlock.ID) -> (inserted: Bool, memberAfterInsert: IRBlock.ID) {
    let inserted = elements.insert(b.rawValue).inserted
    return (inserted, b)
  }

  @discardableResult
  public mutating func update(with b: IRBlock.ID) -> IRBlock.ID? {
    let inserted = elements.insert(b.rawValue).inserted
    return inserted ? b : nil
  }

  @discardableResult
  public mutating func remove(_ b: IRBlock.ID) -> IRBlock.ID? {
    elements.remove(b.rawValue).map({ _ in b })
  }

  public mutating func formUnion(_ other: Self) {
    elements.formUnion(other.elements)
  }

  /// Inserts all the contents `other` into `self`.
  public mutating func formUnion<S: Sequence<IRBlock.ID>>(_ other: S) {
    for b in other { elements.insert(b.rawValue) }
  }

  public func union(_ other: IRBlockSet) -> IRBlockSet {
    var result = self
    result.formUnion(other)
    return result
  }

  public mutating func formIntersection(_ other: Self) {
    elements.formIntersection(other.elements)
  }

  public func intersection(_ other: IRBlockSet) -> IRBlockSet {
    var result = self
    result.formIntersection(other)
    return result
  }

  public mutating func formSymmetricDifference(_ other: Self) {
    elements.formSymmetricDifference(other.elements)
  }

  public func symmetricDifference(_ other: IRBlockSet) -> IRBlockSet {
    var result = self
    result.formSymmetricDifference(other)
    return result
  }

}

/// A hash set that preserves the positions of its elements on mutation.
///
/// You can use `StableSet` instead of `Set` if you want indices in your collection to remain valid
/// after insertion or deletion.
///
/// ```swift
/// var s: StableSet = ["a", "b"]
/// print(s.firstIndex(of: "b")!) // Prints 1
/// s.remove("a")
/// s.insert("c")
/// print(s.firstIndex(of: "b")!) // Prints 1
/// ```
///
/// The order that can be observed through `StableSet`'s conformance to collection is also stable
/// (i.e., preserved under mutation) but note that the index of a removed member may be reused to
/// insert another one.
///
/// Internally, a `StableSet` is a `StableDictionary` whose values are empty.
public struct StableSet<Element: Hashable> {

  /// An empty value.
  private struct Empty: Hashable {}

  /// The contents of the set.
  private var contents: StableDictionary<Element, Empty>

  /// Creates an empty instance.
  public init() {
    self.contents = [:]
  }

  /// Creates an empty instance with enough space to store `minimumCapacity` elements without
  /// allocating new storage.
  public init(minimumCapacity: Int) {
    self.contents = .init(minimumCapacity: minimumCapacity)
  }

  /// Creates an instance with the elements in `members`.
  public init<S: Sequence<Element>>(_ members: S) {
    self.contents = .init(uniqueKeysAndValues: members.lazy.map({ ($0, .init()) }))
  }

  /// `true` iff `self` is empty.
  public var isEmpty: Bool {
    count == 0
  }

  /// The number of elements stored in `self`.
  public var count: Int {
    contents.count
  }

  /// The number of elements that can be stored in `self` without allocating new storage.
  public var capacity: Int {
    contents.capacity
  }

  /// Returns the position of `member` in `self`.
  public func firstIndex(of member: Element) -> Int? {
    contents.index(forKey: member)
  }

  /// Returns `true` iff `member` is contained in `self`.
  public func contains(_ member: Element) -> Bool {
    contents.index(forKey: member) != nil
  }

  /// Adds `member` to `self` if it is not already present and returns `(inserted: i, position: p)`
  /// where `i` is `true` iff the insertion occured and `p` is the position of `member` in `self`.
  @discardableResult
  public mutating func insert(_ member: Element) -> (inserted: Bool, position: Int) {
    contents.assignValue(.init(), forKey: member)
  }

  /// Removes the member stored at `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  @discardableResult
  public mutating func remove(at p: Int) -> Element {
    contents.remove(at: p).key
  }

  /// Removes `member` and returns `true` iff it was present; otherwise, returns `false`.
  @discardableResult
  public mutating func remove(_ member: Element) -> Bool {
    contents.removeValue(forKey: member) != nil
  }

  /// Removes all elements in `self`, preserving storage if `keepCapacity` is `true`.
  public mutating func removeAll(keepingCapacity keepCapacity: Bool = false) {
    contents.removeAll(keepingCapacity: keepCapacity)
  }

  /// Reserves enough space to store `minimumCapacity` elements without allocating new storage.
  public mutating func reserveCapacity(_ minimumCapacity: Int) {
    contents.reserveCapacity(minimumCapacity)
  }

}

extension StableSet: ExpressibleByArrayLiteral {

  /// Creates an instance from an array literal.
  public init(arrayLiteral members: Element...) {
    self.init(members)
  }

}

extension StableSet: Collection {

  public typealias Index = Int

  /// The position of the first key/value pair in `self`.
  public var startIndex: Int {
    contents.startIndex
  }

  /// The position immediately after the position of the last key/value pair in `self`.
  public var endIndex: Int {
    contents.endIndex
  }

  /// Returns the position immediately after `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  public func index(after p: Int) -> Int {
    contents.index(after: p)
  }

  /// Accesses the element at `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  public subscript(p: Int) -> Element {
    _read { yield contents[p].key }
  }

}

extension StableSet: BidirectionalCollection {

  /// Returns the position immediately before `p`.
  ///
  /// - Requires: `p` is a valid position in `self` and different from `self.startIndex`.
  public func index(before p: Int) -> Int {
    contents.index(before: p)
  }

}

extension StableSet: Equatable {}

extension StableSet: Hashable {}

extension StableSet: CustomStringConvertible {

  /// A textual description of `self`.
  public var description: String {
    let members = self.map({ (k) in "\(k)" }).joined(separator: ", ")
    return "[\(members)]"
  }

}

extension StableSet: Sendable where Element: Sendable {}

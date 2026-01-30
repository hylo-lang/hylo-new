import Algorithms

/// An associated array sorted by its keys.
public struct SortedDictionary<Key: Comparable, Value> {

  /// A collection with the keys contained in `self`, ordered so that `i`-th element corresponds
  /// to the `i`-the value in `self`.
  public private(set) var keys: SortedSet<Key>

  /// A collection with the values contained in `self`, ordered so that `i`-th element corresponds
  /// to the `i`-the key in `self`.
  public private(set) var values: ContiguousArray<Value>

  /// Creates an empty instance.
  public init() {
    self.keys = []
    self.values = []
  }

  /// Creates an empty instance with enough space to store `minimumCapacity` pairs without
  /// allocating new storage.
  public init(minimumCapacity: Int) {
    self.keys = .init(minimumCapacity: minimumCapacity)
    self.values = []
    self.values.reserveCapacity(minimumCapacity)
  }

  /// The number of elements that can be stored in `self` without allocating new storage.
  public var capacity: Int {
    keys.capacity
  }

  /// Reserves enough space to store `minimumCapacity` elements without allocating new storage.
  public mutating func reserveCapacity(_ minimumCapacity: Int) {
    keys.reserveCapacity(minimumCapacity)
    values.reserveCapacity(minimumCapacity)
  }

  /// Accesses the value associated to `key`, if any.
  ///
  /// Complexity: O(n log n) where n is the number of key/value pairs in `self`.
  public subscript(key: Key) -> Value? {
    get {
      keys.firstIndex(of: key).map({ (k) in values[k] })
    }
    _modify {
      var v: Value? = nil

      // Is the key already present in the map?
      if let k = keys.firstIndex(of: key) {
        v = values[k]
        defer {
          // Has the value been updated or removed?
          if let w = v.take() {
            values[k] = w
          } else {
            keys.remove(at: k)
            values.remove(at: k)
          }
        }
        yield &v
      }

      // The key is not already in the map.
      else {
        defer {
          // As the value been inserted?
          if let w = v.take() {
            let (_, k) = keys.index(insertingIfAbsent: key)
            values.insert(w, at: k)
          }
        }
        yield &v
      }
    }
  }

}

extension SortedDictionary: ExpressibleByDictionaryLiteral {

  public init(dictionaryLiteral elements: (Key, Value)...) {
    self.init(minimumCapacity: elements.count)
    for (key, value) in elements {
      let (inserted, k) = keys.index(insertingIfAbsent: key)
      precondition(inserted, "duplicate key '\(key)'")
      values.insert(value, at: k)
    }
  }

}

extension SortedDictionary: RandomAccessCollection {

  public typealias Index = Int

  public typealias Element = (key: Key, value: Value)

  public var isEmpty: Bool {
    keys.isEmpty
  }

  public var count: Int {
    keys.count
  }

  public var startIndex: Int {
    0
  }

  public var endIndex: Int {
    keys.count
  }

  public func index(after i: Int) -> Int {
    i + 1
  }

  public subscript(i: Int) -> Element {
    (keys[i], values[i])
  }

}

extension SortedDictionary: Sendable where Key: Sendable, Value: Sendable {}

extension SortedDictionary: Equatable where Value: Equatable {}

extension SortedDictionary: Hashable where Key: Hashable, Value: Hashable {}

extension SortedDictionary: CustomStringConvertible {

  public var description: String {
    "[\(list: self.map({ (k, v) in "\(k): \(v)" }))]"
  }

}

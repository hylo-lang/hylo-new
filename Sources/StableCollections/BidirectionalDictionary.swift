import Utilities

/// An associative container that supports efficient lookup from keys to values and vice versa.
public struct BidirectionalDictionary<Key: Hashable, Value: Hashable>: Hashable {

  /// A table from a key to the position of the corresponding value.
  private var keysAndValues: StableDictionary<Key, Int>

  /// A table from a value to the position of the corresponding key.
  private var valuesAndKeys: StableDictionary<Value, Int>

  /// Creates an empty instance.
  public init() {
    self.keysAndValues = [:]
    self.valuesAndKeys = [:]
  }

  /// Creates an empty instance with enough space to store `minimumCapacity` elements without
  /// allocating new storage.
  public init(minimumCapacity: Int) {
    self.keysAndValues = .init(minimumCapacity: minimumCapacity)
    self.valuesAndKeys = .init(minimumCapacity: minimumCapacity)
  }

  /// Creates an instance with the key/value pairs in `keysAndValues`.
  public init<S: Sequence<(Key, Value)>>(uniqueKeysAndValues keysAndValues: S) {
    self.init(minimumCapacity: keysAndValues.underestimatedCount)
    for (k, v) in keysAndValues {
      let (i, source) = self.keysAndValues.assignValue(0, forKey: k)
      precondition(i)
      let (j, target) = self.valuesAndKeys.assignValue(source, forKey: v)
      precondition(j)
      self.keysAndValues.modify(at: source, { (t) in t = target })
    }
  }

  /// `true` iff `self` is empty.
  public var isEmpty: Bool {
    count == 0
  }

  /// The number of elements stored in `self`.
  public var count: Int {
    keysAndValues.count
  }

  /// The number of elements that can be stored in `self` without allocating new storage.
  public var capacity: Int {
    Swift.min(keysAndValues.capacity, valuesAndKeys.capacity)
  }

  /// Accesses the value assigned to `k`, if any.
  public subscript(key k: Key) -> Value? {
    keysAndValues[k].map({ (i) in valuesAndKeys[i].key })
  }

  /// Accesses the key assigned to `v`, if any.
  public subscript(value v: Value) -> Key? {
    valuesAndKeys[v].map({ (i) in keysAndValues[i].key })
  }

  /// Stores the given key/value pair, updating previous bindings if necessary.
  public mutating func assignValue(_ value: Value, forKey key: Key) {
    // Is the key already bound?
    if let source = keysAndValues.index(forKey: key) {
      let target = keysAndValues[source].value
      if valuesAndKeys[target].key != value {
        valuesAndKeys.remove(at: target)
        finalize(source)
      }
    } else {
      let (inserted, source) = keysAndValues.assignValue(0, forKey: key)
      assert(inserted)
      finalize(source)
    }

    func finalize(_ source: Int) {
      let slot = valuesAndKeys.updateValue(source, forKey: value)
      if let i = slot.former {
        keysAndValues.remove(at: i)
      }
      keysAndValues.modify(at: source, { (p) in p = slot.position })
    }
  }

  /// Removes `key` and returns the value with which it was associated, if any.
  @discardableResult
  public mutating func remove(key: Key) -> Value? {
    if let source = keysAndValues.index(forKey: key) {
      defer { keysAndValues.remove(at: source) }
      return valuesAndKeys.remove(at: keysAndValues[source].value).key
    } else {
      return nil
    }
  }

  /// Removes `value` and returns the key with which it was associated, if any.
  @discardableResult
  public mutating func remove(value: Value) -> Key? {
    if let source = valuesAndKeys.index(forKey: value) {
      defer { valuesAndKeys.remove(at: source) }
      return keysAndValues.remove(at: valuesAndKeys[source].value).key
    } else {
      return nil
    }
  }

  /// Removes all key/value pairs in `self`, preserving storage if `keepCapacity` is `true`.
  public mutating func removeAll(keepingCapacity keepCapacity: Bool = false) {
    keysAndValues.removeAll(keepingCapacity: keepCapacity)
    valuesAndKeys.removeAll(keepingCapacity: keepCapacity)
  }

  /// Reserves enough space to store `minimumCapacity` elements without allocating new storage.
  public mutating func reserveCapacity(_ minimumCapacity: Int) {
    keysAndValues.reserveCapacity(minimumCapacity)
    valuesAndKeys.reserveCapacity(minimumCapacity)
  }

}

extension BidirectionalDictionary: Sendable where Key: Sendable, Value: Sendable {}

extension BidirectionalDictionary: ExpressibleByDictionaryLiteral {

  /// Creates an instance from a dictionary literal.
  public init(dictionaryLiteral elements: (Key, Value)...) {
    self.init(uniqueKeysAndValues: elements)
  }

}

extension BidirectionalDictionary: Collection {

  public typealias Element = (key: Key, value: Value)

  public typealias Index = Int

  public var startIndex: Int {
    keysAndValues.startIndex
  }

  public var endIndex: Int {
    keysAndValues.endIndex
  }

  public func index(after p: Int) -> Int {
    keysAndValues.index(after: p)
  }

  public subscript(p: Int) -> (key: Key, value: Value) {
    let (k, v) = keysAndValues[p]
    return (key: k, value: valuesAndKeys[v].key)
  }

}

extension BidirectionalDictionary: BidirectionalCollection {

  public func index(before p: Int) -> Int {
    keysAndValues.index(before: p)
  }

}

extension BidirectionalDictionary: CustomStringConvertible {

  public var description: String {
    let pairs = self.map({ (k, v) in "\(k): \(v)" }).joined(separator: ", ")
    return "[\(pairs)]"
  }

}

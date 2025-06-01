/// A hash table that preserves the positions of its key/value pairs on mutation.
///
/// You can use `StableDictionary` instead of `Dictionary` if you want indices in your collection
/// to remain valid after insertion or deletion.
///
/// ```swift
/// var s: StableDictionary = ["a": 1, "b": 2]
/// print(s.index(forKey: "b")!) // Prints 1
/// s["a"] = nil
/// s["c"] = 3
/// print(s.index(forKey: "b")!) // Prints 1
/// ```
///
/// The order that can be observed through `StableDictionary`'s conformance to collection is also
/// stable (i.e., preserved under mutation) but note that the index of a removed key/value pair may
/// be reused to insert another one.
///
/// Internally, a `StableDictionary` is composed of an array, which stores key/value pairs, and a
/// hash table mapping key hashes to their position in that array.
public struct StableDictionary<Key: Hashable, Value> {

  /// The header of a stable dictionary.
  private struct Header {

    /// The number of elements in the dictionary.
    var count: Int

    /// The number of buckets in the dictionary.
    var capacity: Int

    /// The position immediately after the last used bucket.
    var end: Int

    /// A table from key hash to the offset of its corresponding bucket.
    var hashToBucket: [Int]

    /// The offsets of the key, value, and hash properties of a bucket.
    ///
    /// These offsets are expensive to re-compute if the types of the keys and/or values are behind
    /// a resilience boundary. Hence, they are cached here.
    let offsets: Bucket.Offsets

    /// Creates an instance with the given properties.
    init(count: Int, capacity: Int, end: Int) {
      self.count = count
      self.capacity = capacity
      self.end = end
      self.hashToBucket = .init(repeating: -1, count: Int(Double(capacity) * 1.25))
      self.offsets = .init()
    }

    /// Updates the hash-to-bucket table to assign `position` to `hash`.
    mutating func assign(position: Int, forHash hash: Int) {
      let h0 = abs(hash) % hashToBucket.count
      var h1 = h0
      while hashToBucket[h1] != -1 {
        h1 = (h1 + 1) % hashToBucket.count
        assert(h1 != h0)
      }
      hashToBucket[h1] = position
    }

  }

  /// A bucket in a stable dictionary.
  private struct Bucket {

    /// The offsets of the stored properties in this data structure.
    struct Offsets {

      /// The offset of `key`.
      let key = UInt16(MemoryLayout<Bucket>.offset(of: \.key)!)

      /// The offset of `value`.
      let value = UInt16(MemoryLayout<Bucket>.offset(of: \.value)!)

      /// The offset of `truncatedHash`.
      let truncatedHash = UInt16(MemoryLayout<Bucket>.offset(of: \.truncatedHash)!)

    }

    /// The key assigned to this bucket.
    let key: Key

    /// The value assigned to this bucket.
    var value: Value

    /// If the bucket is occupied, the 7 lowest bits of `key`'s hash; otherwise, 0.
    var truncatedHash: UInt8

    /// Returns `true` iff `p` refers to a bucket storing a key/value pair, interpreting the raw
    /// bytes of a bucket's using `o`.
    static func isActive(_ p: UnsafeMutablePointer<Bucket>, offsets o: Offsets) -> Bool {
      withMaybeUninitializedHash(of: p, offsets: o, { (h) in (h.pointee & 0x80) == 0x80 })
    }

    /// Returns the result of `action` called with a pointer to the truncated hash of the bucket to
    /// which `p` refers, interpreting the raw bytes of a bucket's using `o`.
    static func withMaybeUninitializedHash<T>(
      of p: UnsafeMutablePointer<Bucket>, offsets o: Offsets,
      _ action: (UnsafeMutablePointer<UInt8>) -> T
    ) -> T {
      let q = UnsafeMutableRawPointer(mutating: p)
      return action((q + Int(o.truncatedHash)).assumingMemoryBound(to: UInt8.self))
    }

    /// Deinitializes the memory referenced by `p`, returning the key/value pair that it stored,
    /// interpreting the raw bytes of a bucket's using `o`.
    static func unsafelyDeinitialize(
      _ p: UnsafeMutablePointer<Bucket>, offsets o: Offsets
    ) -> (key: Key, value: Value) {
      p.pointee.truncatedHash = 0x7f
      let q = UnsafeMutableRawPointer(mutating: p)
      return (
        (q + Int(o.key)).assumingMemoryBound(to: Key.self).move(),
        (q + Int(o.value)).assumingMemoryBound(to: Value.self).move())
    }

  }

  /// The result of a lookup for the position of a key.
  private enum LookupResult {

    /// The key has been found; the position is in the associated value.
    case found(Int)

    /// The key has not been found; the associated value is a valid insertion position.
    case notFound(Int)

  }

  /// The contents of a stable map.
  private class Contents: ManagedBuffer<Header, Bucket> {

    /// Deinitializes `self`.
    deinit { deinitializeElements() }

    /// Deinitialize all elements in `self`.
    func deinitializeElements() {
      withUnsafeMutablePointers { (head, body) in
        let o = head.pointee.offsets
        for i in 0 ..< head.pointee.capacity {
          let s = body.advanced(by: i)
          if Bucket.isActive(s, offsets: o) { s.deinitialize(count: 1) }
          Bucket.withMaybeUninitializedHash(of: s, offsets: o, { (h) in h.initialize(to: 0) })
        }
      }
    }

  }

  /// The key/value pairs stored in `self`.
  private var contents: ManagedBuffer<Header, Bucket>?

  /// Creates an empty instance.
  public init() {
    self.contents = nil
  }

  /// Creates an empty instance with enough space to store `minimumCapacity` elements without
  /// allocating new storage.
  public init(minimumCapacity: Int) {
    self.init()
    self.reserveCapacity(minimumCapacity)
  }

  /// Creates an instance with the key/value pairs in `keysAndValues`.
  public init<S: Sequence<(Key, Value)>>(uniqueKeysAndValues keysAndValues: S) {
    self.init()
    reserveCapacity(keysAndValues.underestimatedCount)
    for (k, v) in keysAndValues {
      let inserted = assignValue(v, forKey: k).inserted
      precondition(inserted)
    }
  }

  /// `true` iff `self` is empty.
  public var isEmpty: Bool {
    count == 0
  }

  /// The number of elements stored in `self`.
  public var count: Int {
    contents?.header.count ?? 0
  }

  /// The number of elements that can be stored in `self` without allocating new storage.
  public var capacity: Int {
    contents?.header.capacity ?? 0
  }

  /// Accesses the value assigned for `key`.
  public subscript(key: Key) -> Value? {
    get {
      switch lookup(key) {
      case .found(let i):
        return self[i].value
      default:
        return nil
      }
    }

    set {
      switch (lookup(key), newValue) {
      case (.found(let i), .some(let value)):
        ensureUnique()
        contents!.withUnsafeMutablePointerToElements { (body) in
          body.advanced(by: i).pointee.value = value
        }
      case (.found(let i), nil):
        remove(at: i)
      case (.notFound(let i), .some(let value)):
        insert(key: key, value: value, at: i)
      case (.notFound, nil):
        break
      }
    }
  }

  /// Returns the position of `key` in `self`.
  public func index(forKey key: Key) -> Int? {
    if case .found(let i) = lookup(key) {
      return i
    } else {
      return nil
    }
  }

  /// Assigns `value` to `key` and returns `(inserted: i, position: p)` where `i` is `true` iff no
  /// value was assigned to `key` and `p` is the position of `key` in `self`.
  @discardableResult
  public mutating func assignValue(
    _ value: Value, forKey key: Key
  ) -> (inserted: Bool, position: Int) {
    switch lookup(key) {
    case .found(let i):
      ensureUnique()
      contents!.withUnsafeMutablePointerToElements { (body) in
        body.advanced(by: i).pointee.value = value
      }
      return (inserted: false, position: i)

    case .notFound(let i):
      insert(key: key, value: value, at: i)
      return (inserted: true, position: i)
    }
  }

  /// Removes the key/value pair stored at `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  @discardableResult
  public mutating func remove(at p: Int) -> (key: Key, value: Value) {
    ensureUnique()
    guard let c = contents else { preconditionFailure("Index out of range") }
    return c.withUnsafeMutablePointers { (head, body) in
      head.pointee.count -= 1
      return Bucket.unsafelyDeinitialize(body.advanced(by: p), offsets: head.pointee.offsets)
    }
  }

  /// Removes the value assigned to `key` in `self`.
  @discardableResult
  public mutating func removeValue(forKey key: Key) -> Value? {
    switch lookup(key) {
    case .found(let i):
      return remove(at: i).value
    case .notFound:
      return nil
    }
  }

  /// Removes all key/value pairs in `self`, preserving storage if `keepCapacity` is `true`.
  public mutating func removeAll(keepingCapacity keepCapacity: Bool = false) {
    if keepCapacity {
      if isKnownUniquelyReferenced(&contents), let c = contents as? Contents {
        c.deinitializeElements()
        c.header = .init(count: 0, capacity: capacity, end: 0)
      } else {
        self = .init(minimumCapacity: capacity)
      }
    } else {
      contents = nil
    }
  }

  /// Reserves enough space to store `minimumCapacity` elements without allocating new storage.
  public mutating func reserveCapacity(_ minimumCapacity: Int) {
    if capacity >= minimumCapacity { return }

    var newCapacity = Swift.max(1, capacity)
    while newCapacity < minimumCapacity {
      newCapacity += newCapacity
    }
    reallocate(withCapacity: newCapacity)
  }

  /// Reallocates `self`'s storage if it isn't unique.
  private mutating func ensureUnique() {
    if isKnownUniquelyReferenced(&contents) { return }
    reallocate(withCapacity: capacity)
  }

  /// Reallocates `self`'s storage with enough space to store `newCapacity` elements.
  ///
  /// - Requires: `newCapacity >= capacity`
  private mutating func reallocate(withCapacity newCapacity: Int) {
    let newContents = Contents.create(minimumCapacity: newCapacity) { _ in
      let (c, e) = contents.map { (c) in (c.header.count, c.header.end) } ?? (0, 0)
      return .init(count: c, capacity: newCapacity, end: e)
    }

    // Copy the current contents.
    contents?.withUnsafeMutablePointers { (_, source) in
      newContents.withUnsafeMutablePointers { (head, target) in
        let o = head.pointee.offsets
        for i in 0 ..< capacity {
          // Copy the bucket.
          let s = source.advanced(by: i)
          let t = target.advanced(by: i)
          let k = Bucket.withMaybeUninitializedHash(of: s, offsets: o) { (h) -> Key? in
            if (h.pointee == 0x00) || (h.pointee == 0x7f) {
              // Bucket is empty or has been occupied.
              Bucket.withMaybeUninitializedHash(of: t, offsets: o) { (g) in
                g.initialize(to: h.pointee)
              }
              return nil
            } else {
              // Bucket is occupied.
              t.initialize(from: s, count: 1)
              return s.pointee.key
            }
          }

          // Update the hash-to-bucket relation if the bucket is occupied.
          if let key = k {
            head.pointee.assign(position: i, forHash: key.hashValue)
          } else {
            Bucket.withMaybeUninitializedHash(of: t, offsets: o, { (g) in g.initialize(to: 0) })
          }
        }
      }
    }

    // Zero-initialize the additional storage.
    newContents.withUnsafeMutablePointers { (head, target) in
      let o = head.pointee.offsets
      for i in count ..< newCapacity {
        Bucket.withMaybeUninitializedHash(of: target.advanced(by: i), offsets: o) { (h) in
          h.initialize(to: 0)
        }
      }
    }

    contents = newContents
  }

  /// Returns the position of `key` in `self`.
  private func lookup(_ key: Key) -> LookupResult {
    contents?.withUnsafeMutablePointers { (head, body) -> LookupResult in
      let hash = key.hashValue
      let truncatedHash = UInt8(hash & 0xff) | 0x80

      let h0 = abs(hash) % head.pointee.hashToBucket.count
      var h1 = h0
      var emptyBucket = -1
      repeat {
        let position = head.pointee.hashToBucket[h1]
        let h2 = body[position].truncatedHash

        if position == -1 {
          // Hash is not stored.
          break
        } else if (h2 == truncatedHash) && body[position].key == key {
          // Bucket found.
          return .found(position)
        } else if h2 == 0 {
          // Key is not contained.
          break
        } else if h2 == 0x7f {
          // Bucket has been occupied.
          emptyBucket = position
        }

        // Keep probing.
        h1 = (h1 + 1) % head.pointee.hashToBucket.count
      } while h1 != h0
      return .notFound(emptyBucket == -1 ? head.pointee.end : emptyBucket)
    } ?? .notFound(0)
  }

  /// Inserts the given key/value pair at `p`.
  private mutating func insert(key: Key, value: Value, at p: Int) {
    reserveCapacity(Swift.max(count + 1, p))
    ensureUnique()
    contents!.withUnsafeMutablePointers { (head, body) in
      let hash = key.hashValue
      body.advanced(by: p).initialize(
        to: .init(key: key, value: value, truncatedHash: UInt8(hash & 0xff) | 0x80))
      head.pointee.assign(position: p, forHash: hash)
      head.pointee.count += 1
      if (p == head.pointee.end) { head.pointee.end = p + 1 }
    }
  }

}

extension StableDictionary: ExpressibleByDictionaryLiteral {

  /// Creates an instance from a dictionary literal.
  public init(dictionaryLiteral elements: (Key, Value)...) {
    self.init(uniqueKeysAndValues: elements)
  }

}

extension StableDictionary: Collection {

  public typealias Element = (key: Key, value: Value)

  public typealias Index = Int

  /// The position of the first key/value pair in `self`.
  public var startIndex: Int {
    contents.map { (c) in
      c.withUnsafeMutablePointers { (head, body) in
        let o = head.pointee.offsets
        for i in 0 ..< head.pointee.end {
          if Bucket.isActive(body.advanced(by: i), offsets: o) { return i }
        }
        return head.pointee.end
      }
    } ?? 0
  }

  /// The position immediately after the position of the last key/value pair in `self`.
  public var endIndex: Int {
    contents?.header.end ?? 0
  }

  /// Returns the position immediately after `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  public func index(after p: Int) -> Int {
    guard let c = contents else { preconditionFailure("Index out of range") }
    return c.withUnsafeMutablePointers { (head, body) in
      precondition((p >= 0) && (p < head.pointee.end), "Index out of range")
      let o = head.pointee.offsets
      for i in (p + 1) ..< head.pointee.end {
        if Bucket.isActive(body.advanced(by: i), offsets: o) { return i }
      }
      return head.pointee.end
    }
  }

  /// Accesses the key/value pair at `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  public subscript(p: Int) -> (key: Key, value: Value) {
    guard let c = contents else { preconditionFailure("Index out of range") }
    return c.withUnsafeMutablePointers { (head, body) in
      precondition((p >= 0) && (p < head.pointee.end), "Index out of range")
      let o = head.pointee.offsets
      let s = body.advanced(by: p)
      precondition(Bucket.isActive(s, offsets: o), "Index out of range")
      return (s.pointee.key, s.pointee.value)
    }
  }

}

extension StableDictionary: BidirectionalCollection {

  /// Returns the position immediately before `p`.
  ///
  /// - Requires: `p` is a valid position in `self` and different from `self.startIndex`.
  public func index(before p: Int) -> Int {
    guard let c = contents else { preconditionFailure("Index out of range") }
    return c.withUnsafeMutablePointers { (head, body) in
      precondition((p >= 0) && (p <= head.pointee.end), "Index out of range")
      let o = head.pointee.offsets
      for i in (0 ..< p).reversed() {
        if Bucket.isActive(body.advanced(by: i), offsets: o) { return i }
      }
      preconditionFailure("Index out of range")
    }
  }

}

extension StableDictionary: Equatable where Value: Equatable {

  /// Returns `true` iff `l` is equal to `r`.
  public static func == (l: Self, r: Self) -> Bool {
    (l.contents === r.contents) || l.elementsEqual(r) { (a, b) in
      (a.key == b.key) && (a.value == b.value)
    }
  }

}

extension StableDictionary: Hashable where Value: Hashable {

  /// Adds a hash of the salient parts of `self` into `hasher`.
  public func hash(into hasher: inout Hasher) {
    for (k, v) in self {
      hasher.combine(k)
      hasher.combine(v)
    }
  }

}

extension StableDictionary: CustomStringConvertible {

  /// A textual description of `self`.
  public var description: String {
    let pairs = self.map({ (k, v) in "\(k): \(v)"}).joined(separator: ", ")
    return "[\(pairs)]"
  }

}

extension StableDictionary: @unchecked Sendable where Key: Sendable, Value: Sendable {}

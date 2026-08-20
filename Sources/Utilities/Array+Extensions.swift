extension Array {

  /// Creates an instance with enough storage to store `n` elements without allocating new memory.
  public init(minimumCapacity n: Int) {
    self.init()
    self.reserveCapacity(n)
  }

  /// Creates an array with the value of `head` followed by the contents of `suffix`.
  public init<S: Sequence<Element>>(_ head: Element, prependedTo suffix: S) {
    self.init(minimumCapacity: suffix.underestimatedCount + 1)
    self.append(head)
    self.append(contentsOf: suffix)
  }

  /// Creates an array with the contents of `prefix` followed by `back`.
  public init<S: Sequence<Element>>(_ prefix: S, terminatedBy back: Element) {
    self.init(minimumCapacity: prefix.underestimatedCount + 1)
    self.append(contentsOf: prefix)
    self.append(back)
  }

  /// Creates an array with the contents of `e`, if any.
  public init(unwrapping e: Element?) {
    if let x = e {
      self = [x]
    } else {
      self = []
    }
  }

  /// Returns the contents of `self` suffixed by `back`.
  public consuming func appending(_ back: Element) -> Self {
    var xs = self
    xs.append(back)
    return xs
  }

  /// Appends `n` copies of `back` at the end of `self`.
  public mutating func append(_ back: Element, count n: Int) {
    append(contentsOf: repeatElement(back, count: n))
  }

}

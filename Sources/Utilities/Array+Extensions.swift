extension Array {

  /// Creates an instance with enough storage to store `n` elements without allocating new memory.
  public init(minimumCapacity n: Int) {
    self.init()
    self.reserveCapacity(n)
  }

  /// Creates an array with the value of `head` followed by the contents of `tail`.
  public init<S: Sequence<Element>>(_ head: Element, prependedTo tail: S) {
    self.init(minimumCapacity: tail.underestimatedCount + 1)
    self.append(head)
    self.append(contentsOf: tail)
  }

  /// Creates an array with the contents of `e`, if any.
  public init(contentsOf e: Element?) {
    if let x = e {
      self = [x]
    } else {
      self = []
    }
  }

}

extension StringProtocol {

  /// Returns `self` indented by two spaces.
  public var indented: String {
    (self.split(whereSeparator: \.isNewline) as [SubSequence])
      .map({ (line) in "  " + line })
      .joined(separator: "\n")
  }

  /// Returns the indices of the start of each line, in order.
  public func lineBoundaries() -> [Index] {
    var r = [startIndex]
    var remainder = self[...]
    while !remainder.isEmpty, let i = remainder.firstIndex(where: \.isNewline) {
      let j = index(after: i)
      r.append(j)
      remainder = remainder[j...]
    }
    return r
  }

}

extension StringProtocol where SubSequence == Substring {

  /// Returns the longest prefix of `self` that doesn't contain a newline.
  public var firstLine: Substring {
    prefix(while: { (c) in !c.isNewline })
  }

}

extension Substring {

  /// Returns `true` and removes the first element in `self` if it satisfies `predicate`.
  /// Otherwise, returns `false`.
  ///
  /// - Complexity: O(1).
  public mutating func removeFirst(if predicate: (Character) -> Bool) -> Bool {
    if let h = first, predicate(h) {
      removeFirst()
      return true
    } else {
      return false
    }
  }

  /// Returns `true` and removes the first element in `self` if it is equal to `pattern`.
  /// Otherwise, returns `false`.
  ///
  /// - Complexity: O(1).
  public mutating func removeFirst(if pattern: Character) -> Bool {
    if first == pattern {
      removeFirst()
      return true
    } else {
      return false
    }
  }

}

extension String.StringInterpolation {

  /// Appends the string descriptions of the elements in `list` separated by `separator`.
  public mutating func appendInterpolation<L: Sequence>(
    list: L, joinedBy separator: String = ", "
  ) {
    appendLiteral(list.descriptions(joinedBy: separator))
  }

}

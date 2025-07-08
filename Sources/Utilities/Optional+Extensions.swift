extension Optional {

  /// Returns the value wrapped in `self`, which is not `nil`, and assigns `self` to `nil`.
  public mutating func sink() -> Wrapped {
    defer { self = nil }
    return self!
  }

  /// If `self` is `nil`, wraps and returns `newValue`; otherwise, returns the wrapped value.
  public mutating func wrapIfEmpty(
    _ newValue: @autoclosure () throws -> Wrapped
  ) rethrows -> Wrapped {
    if let wrapped = self {
      return wrapped
    } else {
      let wrapped = try newValue()
      self = wrapped
      return wrapped
    }
  }

  /// Returns the value wrapped in `self` or throws `error` if `self` is `nil`.
  public func unwrapOrThrow<E: Error>(_ error: @autoclosure () -> E) throws -> Wrapped {
    if let wrapped = self { wrapped } else { throw error() }
  }

  /// Returns the value wrapped in `optional` or throws `error` if `optional` is `nil`.
  public static func ?? <E: Error>(optional: Self, error: @autoclosure () -> E) throws -> Wrapped {
    try optional.unwrapOrThrow(error())
  }

  /// Returns the value wrapped in `optional` or calls `trap` if `optional` is `nil`.
  public static func ?? (optional: Self, trap: @autoclosure () -> Never) -> Wrapped {
    if let wrapped = optional { wrapped } else { trap() }
  }

}

// infix operator >>= : BitwiseShiftPrecedence

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

  /// Returns `true` iff `self` wraps a value satisfying `predicate`.
  public func satisfies(_ predicate: (Wrapped) throws -> Bool) rethrows -> Bool {
    try self.map(predicate) ?? false
  }

  /// Returns the value wrapped in `optional` or throws `error` if `optional` is `nil`.
  public static func ?? <E: Error>(optional: Self, error: @autoclosure () -> E) throws -> Wrapped {
    try optional.unwrapOrThrow(error())
  }

  /// Returns the value wrapped in `optional` or calls `trap` if `optional` is `nil`.
  public static func ?? (optional: Self, trap: @autoclosure () -> Never) -> Wrapped {
    if let wrapped = optional { wrapped } else { trap() }
  }

  /// Returns the result of calling `transform` on the value wrapped in `self` iff there is one.
  /// Otherwise, returns `nil.`
  public static func >>= <T>(optional: Self, _ transform: (Wrapped) throws -> T?) rethrows -> T? {
    try optional.flatMap(transform)
  }

  /// Returns the result of calling `transform` on the value wrapped in `self` iff there is one.
  /// Otherwise, returns `nil.`
  public static func >>= <T>(optional: Self, _ path: KeyPath<Wrapped, T>) -> T? {
    optional.flatMap({ (w) in w[keyPath: path] })
  }

}

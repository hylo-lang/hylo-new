/// Returns the application of `action` on an immutable projection of `value`.
public func read<T, U>(_ value: T, _ action: (T) throws -> U) rethrows -> U {
  try action(value)
}

/// Returns the application of `action` on a mutable projection of `value`.
public func modify<T, U>(_ value: inout T, _ action: (inout T) throws -> U) rethrows -> U {
  try action(&value)
}

/// Returns the application of `action` on a mutable projection of `value` as an instance of `T`.
public func modify<T, U>(
  _ value: inout Any, as: T.Type, _ action: (inout T) throws -> U
) rethrows -> U {
  var v = consume value as! T
  defer { value = v }
  return try action(&v)
}

/// Assigns `value` to the result of applying `transform` on it.
public func update<T>(_ value: inout T, with transform: (T) throws -> T) rethrows {
  value = try transform(value)
}

import Archivist

/// A type-erasing container for type trees.
internal struct AnyTypeTree: Sendable {

  /// The node wrapped in this container.
  internal let wrapped: any TypeTree

  /// Creates an instance wrapping `n`.
  internal init(_ n: any TypeTree) {
    self.wrapped = n
  }

}

extension AnyTypeTree: Equatable {

  internal static func == (l: Self, r: Self) -> Bool {
    l.wrapped.equals(r.wrapped)
  }

}

extension AnyTypeTree: Hashable {

  internal func hash(into hasher: inout Hasher) {
    wrapped.hash(into: &hasher)
  }

}

extension AnyTypeTree: Archivable {

  internal init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let k = try archive.read(TypeTag.self, in: &context)
    self = .init(try archive.read(k.value, in: &context))
  }

  internal func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(TypeTag(type(of: wrapped)), in: &context)
    try archive.write(wrapped, in: &context)
  }

}

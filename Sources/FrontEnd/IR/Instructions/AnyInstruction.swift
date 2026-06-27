import Archivist

/// A type-erasing container for IR instructions.
internal struct AnyInstruction: Sendable {

  /// The instruction wrapped in this container.
  internal let wrapped: any Instruction

  /// Creates an instance wrapping `n`.
  internal init(_ n: any Instruction) {
    self.wrapped = n
  }

}

extension AnyInstruction: Equatable {

  internal static func == (l: Self, r: Self) -> Bool {
    l.wrapped.equals(r.wrapped)
  }

}

extension AnyInstruction: Hashable {

  internal func hash(into hasher: inout Hasher) {
    wrapped.hash(into: &hasher)
  }

}

extension AnyInstruction: Archivable {

  internal init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let k = try archive.read(InstructionTag.self, in: &context)
    self = .init(try archive.read(k.value, in: &context))
  }

  internal func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(InstructionTag(type(of: wrapped)), in: &context)
    try archive.write(wrapped, in: &context)
  }

}

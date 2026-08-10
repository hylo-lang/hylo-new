/// A value occuring during program execution.
struct RuntimeValue {

  /// The bytes of value, preceded by zero or more bytes of padding to satisfy
  /// its alignment.
  private var storage: [UInt8]

  /// The number of bytes before the value logically begins.
  private let baseOffset: Int

  /// Creates an instance from its bytes representation `bytes`, with alignment `a`.
  public init(bytes: [UInt8], havingAlignment a: Int) {
    storage = .init(repeating: 0, count: bytes.count)

    // If we didn't get suitably-aligned storage, allocate enough to
    // ensure we can find a suitably-aligned region of the right
    // size.
    if storage.withUnsafeBytes({ UInt(bitPattern: $0.baseAddress) % UInt(a) != 0 }) {
      storage = .init(repeating: 0, count: bytes.count + a - 1)
    }

    baseOffset = storage.withUnsafeBytes { $0.firstOffsetAligned(to: a) }
    storage[baseOffset...] = bytes[...]
  }

}

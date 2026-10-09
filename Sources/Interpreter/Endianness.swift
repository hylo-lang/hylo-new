/// The order in which the bytes of multi-byte values are arranged in memory.
public enum Endianness {

  /// Places the least significant byte at the lowest address.
  case little

  /// Places the most significant byte at the lowest address.
  case big
}

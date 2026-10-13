/// The order in which the bytes of multi-byte values are arranged in memory.
public enum Endianness {

  /// The least significant byte is first in memory.
  case lsbFirst

  /// The most significant byte is first in memory.
  case msbFirst

}

import Archivist
import BigInt
import Foundation
import StableCollections

extension ReadableArchive {

  /// Reads an address suitable for identifying elements in a list of `T`.
  internal mutating func read<T>(
    _: List<T>.Address.Type, in _: inout Any
  ) throws -> List<T>.Address {
    try .init(readSignedLEB128())
  }

  /// Reads a URL.
  internal mutating func read(_: URL.Type, in _: inout Any) throws -> URL {
    try URL(string: self.read(String.self))!
  }

  /// Reads a big integer.
  internal mutating func read(_: BigInt.Type, in context: inout Any) throws -> BigInt {
    let count = try Int(readUnsignedLEB128())
    return try withUnsafeTemporaryAllocation(of: UInt8.self, capacity: count) { (data) in
      for i in 0 ..< count {
        try data.initializeElement(at: i, to: readByte())
      }
      return BigInt(UnsafeRawBufferPointer(data))
    }
  }

}

extension WriteableArchive {

  /// Writes `d` to the archive, ordering key/value pairs according to `comparator`, updating
  /// `context` with the srialization state.
  internal mutating func write<K: Archivable, V: Archivable, C: Comparable>(
    _ d: [K: V], in context: inout Any,
    sortedBy comparator: KeyPath<(key: K, value: V), C>
  ) throws {
    try self.write(contentsOf: d.sorted(by: comparator), in: &context) { (x, a, c) in
      try x.key.write(to: &a, in: &c)
      try x.value.write(to: &a, in: &c)
    }
  }

  /// Writes `a` to the archive.
  internal mutating func write<T>(_ a: List<T>.Address, in _: inout Any) throws {
    try write(a.rawValue)
  }

  /// Writes `u` to the archive.
  internal mutating func write(_ u: URL, in _: inout Any) throws {
    try write(u.absoluteString)
  }

  /// Writes `n` to the archive.
  internal mutating func write(_ n: BigInt, in context: inout Any) throws {
    let data = n.serializeToBuffer()
    defer { data.deallocate() }
    write(contentsOf: data, in: &context) { (b, a, _) in
      a.write(byte: b)
    }
  }

}

import Archivist
import StableCollections

extension ReadableArchive {

  /// Reads an address suitable for identifying elements in a list of `T`.
  internal mutating func read<T>(address _: List<T>.Address.Type) throws -> List<T>.Address {
    try .init(readSignedLEB128())
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
  internal mutating func write<T>(_ a: List<T>.Address) throws {
    try write(a.rawValue)
  }

}

extension Archivable {

  func _serialized() throws -> String {
    var a = WriteableArchive(BinaryBuffer())
    try a.write(self)
    return a.finalize().description
  }

}

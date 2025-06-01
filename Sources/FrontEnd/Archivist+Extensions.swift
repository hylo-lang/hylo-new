import Archivist

extension WriteableArchive {

  internal mutating func write<K: Archivable, V: Archivable, C: Comparable>(
    _ d: [K: V], in context: inout Any,
    sortedBy comparator: KeyPath<(key: K, value: V), C>
  ) throws {
    try d.sorted(by: comparator).write(to: &self) { (e, a) in
      try a.write(e.key, in: &context)
      try a.write(e.value, in: &context)
    }
  }

}

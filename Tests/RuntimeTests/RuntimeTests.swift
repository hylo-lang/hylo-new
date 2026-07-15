import XCTest

fileprivate typealias Size = UInt32
fileprivate typealias Alignment = UInt16
fileprivate typealias MemberIndex = UInt32
fileprivate typealias WitnessIndex = UInt32
fileprivate typealias MemberCount = UInt32
fileprivate typealias VoidPointer = UnsafePointer<UInt8>?

/// Layout of the first part of type witnesses.
fileprivate typealias TypeWitnessHeader = (
  VoidPointer, // ?
  Size,                 // size
  Alignment             // alignment
)

/// Fatal error unless TypeWitnessHeader lays out in declaration
/// order in Hylo.
func checkLayoutRequirements() {
  precondition(
    MemoryLayout<VoidPointer>.alignment >= MemoryLayout<Size>.alignment,
    "Assumptions about TypeWitnessHeader tuple layout violated"
  )
  precondition(
    MemoryLayout<Size>.alignment >= MemoryLayout<Alignment>.alignment,
    "Assumptions about TypeWitnessHeader tuple layout violated"
  )
}

let layoutRequirementsChecked: () = checkLayoutRequirements()

fileprivate extension Alignment {

  /// Returns the first n >= i that is a multiple of self
  func first_aligned_offset(starting_from i: Size) -> Size {
    let a = Size(self)
    // The distance from i to the nearest aligned offset <= i.
    let excess = i % a
    return excess == 0 ? i : i - excess + a
  }

}

/// Notionally, the type of a member of a record type
fileprivate typealias RecordMemberType = UnsafePointer<TypeWitnessHeader>

fileprivate extension RecordMemberType {

  /// Returns the size of an instance
  func size() -> Size { self[0].1 }

  /// Returns the alignment of an instance
  func alignment() -> UInt16 { self[0].2 }

}

/// Notionally, a collection of Witnesses of unspecified size.
fileprivate struct RecordLayout {
  typealias Count = UInt32
  typealias Index = UInt32

  let start: UnsafeMutablePointer<RecordMemberType>
  var count: Count
}

fileprivate extension RecordLayout {

  /// Accesses the nth element.
  subscript(n: MemberIndex) -> RecordMemberType {
    get { start[Int(n)] }
    nonmutating set { start[Int(n)] = newValue }
  }

  /// Discard element n and any with lesser alignments, or with the
  /// same alignment occurring at an initial index >= n.
  mutating func retain_only_elements(that_lay_out_before_element n: Index) {
    let nth_alignment = self[n].alignment()
    // Next element to process.
    var i: Count = 0
    // Skip over initial retained sequence.
    while i < n && self[i].alignment() >= nth_alignment {
      i += 1
    }
    // The number of elements to retain.
    var new_count = i

    // ith is not retained, either because it is nth or because its
    // alignment was too low.  Therefore we have a hole at new_count
    // that we can write into.
    i += 1

    // From here on out, i > new_count

    // elements before the nth are retained iff they have greater or
    // equal alignment.
    while i < n {
      if self[i].alignment() >= nth_alignment {
        self[new_count] = self[i]
        new_count += 1
      }
      i += 1
    }

    // Nth element is discarded.
    if i == n { i += 1 }

    // elements after the nth are retained iff they have greater
    // alignment.
    while i < count {
      if self[i].alignment() > nth_alignment {
        self[new_count] = self[i]
        new_count += 1
      }
      i += 1
    }

    count = new_count
  }

  /// Stably sorts the elements in decreasing alignment order.
  ///
  /// - Complexity: *O*(`count`²) (insertion sort)
  mutating func stable_sort_by_decreasing_alignment() {
    // Nothing to sort
    if count < 2 { return }

    var prior_alignment = self[0].alignment()

    var i: Index = 1
    while i < count {
      // invariant: elements 0..<i are sorted.

      let w = self[i]
      let w_alignment = w.alignment()

      if prior_alignment >= w_alignment {
        // w was already in the right place
        prior_alignment = w_alignment
      } else {
        // We moved ith out of self, so there's a hole at i.

        // The hole position,
        var j = i
        // Move the hole toward the front (by repeatedly moving an
        // element into the hole) until it's where ith should go.

        while true {
          // Move jth back one, into the hole, leaving a hole at j - 1.
          self[j] = self[j - 1]
          j -= 1
          if j == 0 || self[j - 1].alignment() >= w_alignment { break }
        }
        // put w in the hole.
        self[j] = w
      }

      i += 1
    }
  }

  /// Returns the size required to store properties of types given by
  /// the elements of `self` in that order.
  func sizeForCurrentOrder() -> Size {
    var r: Size = 0
    var i: Index = 0
    while i < count {
      let w = self[i]
      let position = w.alignment().first_aligned_offset(starting_from: r)
      r = position + w.size()
      i += 1
    }
    return r
  }

  /// Returns the offset where the initial `nth` element would appear.
  ///
  /// Mutates `self` in arbitrary ways
  mutating func offset_of_member(_ n: Index) -> Size {
    let nth_alignment = self[n].alignment()
    retain_only_elements(that_lay_out_before_element: n)
    stable_sort_by_decreasing_alignment()
    return nth_alignment.first_aligned_offset(
      starting_from: sizeForCurrentOrder())
  }

}

private extension Array<TypeWitnessHeader> {

  /// Passes a `RecordLayout` for the types corresponding to the
  /// elements to `body` and returns the result.
  ///
  /// Always results in a record layout containing no duplicate
  /// TypeWitnessHeader pointers, so when used in testing stability
  /// checks are strong: each element has an identity distinct from
  /// its alignment.
  func withRecordLayout<R>(_ body: (inout RecordLayout)->R) -> R {
    withUnsafeBufferPointer { headers in
      var storage = headers.indices.map { headers.baseAddress! + $0 }
      return storage.withUnsafeMutableBufferPointer { types in
        var l = RecordLayout.init(
          start: types.baseAddress!, count: UInt32(types.count))
        return body(&l)
      }
    }
  }

}

private extension RecordLayout {

  /// Passes an `UnsafeBufferPointer` containing the member types (in
  /// order) to `b` and returns the result.
  func withUnsafeBufferPointer<R>(
    _ body: (UnsafeBufferPointer<RecordMemberType>) -> R
  ) -> R {
    return body(UnsafeBufferPointer.init(start: start, count: Int(count)))
  }

  /// Returns an array containing the member types in order.
  func array() -> [RecordMemberType] {
    withUnsafeBufferPointer { Array($0) }
  }
}

final class LayoutTests: XCTestCase {

  fileprivate func w(_ alignment: Alignment, size: Size = 1) -> TypeWitnessHeader {
    (nil, size, alignment)
  }

  func testStableSort() {
    func check(_ alignments: [Alignment]) {
      let x = alignments.map { w($0) }
      x.withRecordLayout { l in
        let original = l.array()
        l.stable_sort_by_decreasing_alignment()
        let sorted = l.array()
        // Swift's sort is stable.
        let expected = original.sorted { a, b in a.alignment() > b.alignment() }
        XCTAssertEqual(
          sorted, expected,
          """
            original \(original.map { $0.alignment() })

            \(sorted.map { $0.alignment() })
            vs
            \(expected.map { $0.alignment() })
            
          """
        )
      }
    }

    check([3])
    check([3, 3])
    check([3, 1, 3, 4, 4, 4, 2, 7, 4, 6])
    check([3, 9, 3, 8, 4, 1, 2, 7, 4, 6])

    // Randomly generated via
    // for _ in 0..<20 {
    //   let a = (0..<Int.random(in: 2..<10)).map { _ in Int.random(in: 1..<10) }
    //   print("check(\(a))")
    // }

    check([4, 8, 8, 4])
    check([5, 7, 1])
    check([5, 5, 8, 9, 8, 5])
    check([6, 8, 4, 5, 8])
    check([6, 1])
    check([5, 2, 3, 4, 9, 6])
    check([5, 2, 4, 5, 3])
    check([5, 9])
    check([4, 1, 4, 2, 3, 4, 8, 8])
    check([1, 8, 5])
    check([8, 7, 1, 1, 3, 7, 3, 5, 9])
    check([9, 3, 8])
    check([6, 2, 6, 7, 5, 3, 7, 6])
    check([2, 2, 6, 1, 5, 7])
    check([4, 1, 6, 3, 3, 8, 9, 5, 1])
    check([2, 5, 9])
    check([5, 2])
    check([9, 2, 5, 3, 2])
    check([1, 1, 7])
    check([7, 7, 3, 8, 2, 3, 7, 6])
  }

  func testRetainPriorLayoutElements() {
    func checkMember(_ n: MemberIndex, in x: [TypeWitnessHeader]) {
      x.withRecordLayout { l in
        let original = l.array()
        l.retain_only_elements(that_lay_out_before_element: n)
        let retained = l.array()
        let expected = original.indices.filter { i in
          original[i].alignment() > original[Int(n)].alignment()
          || original[i].alignment() == original[Int(n)].alignment() && i < n
        }.map { original[$0] }

        XCTAssertEqual(
          retained, expected,
          """
            n = \(n)
            original = \(original.map { $0.alignment() })

            \(retained.map { $0.alignment() })
            vs
            \(expected.map { $0.alignment() })

          """
        )
      }
    }

    func check(_ alignments: [Alignment]) {
      let x = alignments.map { w($0) }
      for n in 0..<x.count {
        checkMember(MemberIndex(n), in: x)
      }
    }

    check([3])
    check([3, 3])
    check([1, 3])
    check([3, 1])

    check([3, 1, 3, 4, 4, 4, 2, 7, 4, 6])
    check([3, 9, 3, 8, 4, 1, 2, 7, 4, 6])

    // Randomly generated via
    // for _ in 0..<20 {
    //   let a = (0..<Int.random(in: 2..<10)).map { _ in Int.random(in: 1..<10) }
    //   print("check(\(a))")
    // }

    check([6, 4, 2, 1, 3, 8, 7, 9, 1])
    check([6, 5, 9, 4, 5, 9, 9, 4])
    check([5, 8, 4, 5, 4])
    check([5, 5, 5, 6, 6, 7, 1])
    check([6, 5, 3])
    check([5, 3, 4, 9, 7, 8, 5, 5, 7])
    check([9, 7, 2, 5, 6, 6])
    check([7, 6, 2, 2, 7, 1])
    check([2, 7])
    check([9, 3, 2, 5, 7, 1])
    check([1, 2, 6, 7, 6, 9, 4])
    check([9, 4, 5, 6, 6])
    check([5, 1, 6, 3, 2])
    check([7, 5, 1, 5, 5, 3])
    check([9, 8, 6, 9])
    check([5, 6, 4, 1, 2, 4])
    check([6, 7, 4, 1, 1, 8])
    check([6, 5])
    check([3, 7, 7, 3])
    check([8, 5, 2, 1, 1, 6])

  }

  func testSizeForCurrentOrder() {

    func check(_ sizeAlign: [(Size, Alignment)]) {
      let x = sizeAlign.map { sa in w(sa.1, size: sa.0) }

      x.withRecordLayout { l in
        let original = l.array()
        let size = l.sizeForCurrentOrder()
        var total: Size = 0
        for t in original {
          // distance to the nearest alignment point <= expected
          let x = total % Size(t.alignment())
          let position = x == 0 ? total : total - x + Size(t.alignment())
          total = position + t.size()
        }
        XCTAssertEqual(
          size, total,
          """
            original \(original.map { $0.alignment() })

          """)
      }
    }

    // for _ in 0..<40 {
    //   let a = (0..<Int.random(in: 2..<10))
    //     .map { _ in (Int.random(in: 0..<10), Int.random(in: 1..<10)) }
    //   print("    check(\(a))")
    // }

    check([(9, 1), (6, 1), (1, 9)])
    check([(5, 7), (8, 3), (4, 7), (2, 2), (9, 9), (6, 4)])
    check([(7, 6), (1, 7), (6, 1), (2, 2), (7, 4), (3, 8), (8, 4), (8, 3)])
    check([(2, 9), (6, 1), (8, 8), (6, 1)])
    check([(0, 1), (7, 9)])
    check([(7, 2), (9, 5)])
    check([(5, 8), (6, 3), (4, 8), (2, 4), (6, 9), (1, 1), (0, 5), (7, 1)])
    check([(8, 1), (1, 3), (1, 9), (0, 2), (1, 7), (4, 8), (3, 6), (6, 8)])
    check([(1, 7), (6, 6), (0, 2)])
    check([(0, 6), (8, 3), (5, 6), (9, 9), (0, 3), (5, 5), (3, 5), (5, 2)])
    check([(2, 8), (6, 1), (3, 7), (4, 6), (7, 5)])
    check([(2, 5), (9, 9)])
    check([(4, 5), (1, 4)])
    check([(1, 4), (7, 9), (3, 9), (4, 4), (2, 3), (9, 5), (5, 8)])
    check([(1, 3), (3, 1), (9, 6), (7, 1), (5, 8), (0, 6), (9, 5), (2, 5), (4, 1)])
    check([(4, 8), (8, 9), (0, 1), (1, 5), (9, 7), (4, 2), (9, 6), (1, 8)])
    check([(4, 8), (9, 5), (7, 8), (0, 9), (2, 6), (4, 2), (9, 1), (7, 2), (7, 4)])
    check([(9, 4), (6, 1), (3, 8), (5, 6), (5, 4), (8, 3)])
    check([(0, 1), (3, 5), (2, 7), (6, 3), (5, 6), (4, 8), (3, 8)])
    check([(9, 5), (2, 7), (2, 3), (5, 3), (7, 7)])
    check([(2, 5), (8, 9), (4, 1), (3, 2), (1, 1), (4, 7), (8, 9), (5, 8), (6, 6)])
    check([(8, 1), (8, 7)])
    check([(4, 5), (8, 4), (7, 6)])
    check([(5, 9), (4, 6), (0, 8), (4, 5), (1, 1), (4, 7)])
    check([(4, 7), (7, 5), (0, 4), (3, 9)])
    check([(9, 9), (2, 3), (5, 2), (7, 6)])
    check([(4, 7), (8, 3), (8, 5), (8, 3)])
    check([(8, 8), (9, 4)])
    check([(2, 8), (3, 5), (9, 7), (2, 7), (9, 2), (4, 4), (3, 9), (6, 2), (5, 6)])
    check([(8, 8), (3, 5), (7, 7)])
    check([(1, 4), (3, 8), (1, 6), (9, 5), (5, 1), (6, 4), (2, 7), (7, 1), (3, 4)])
    check([(3, 8), (7, 5), (0, 8), (7, 6), (2, 4)])
    check([(6, 9), (3, 9), (1, 6), (0, 5), (8, 6), (4, 7), (9, 1), (8, 6)])
    check([(6, 2), (1, 5), (4, 4), (2, 1), (1, 2), (8, 1), (9, 7), (8, 7)])
    check([(7, 8), (6, 3), (3, 3), (4, 5), (0, 8), (8, 8), (4, 1)])
    check([(9, 8), (6, 8)])
    check([(0, 5), (3, 6), (1, 4), (7, 8), (9, 3)])
    check([(6, 6), (7, 7)])
    check([(9, 4), (4, 7), (0, 4), (6, 5)])
    check([(6, 7), (1, 1)])
  }
  
}

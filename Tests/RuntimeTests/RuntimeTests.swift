import XCTest
import Foundation

// ========================= NOTE ===========================
// Many of the names in this file use Hylo naming convention
// to make checking the correspondence of code easier.
// ==========================================================

fileprivate typealias Size = UInt32
fileprivate typealias Alignment = UInt16
fileprivate typealias StringPointer = UnsafePointer<UInt8>?

/// Layout of the first part of type witnesses.
private struct TypeWitnessHeader {
  // TODO: verify that the type of `description` is correct.
  // see https://github.com/hylo-lang/hylo-new/issues/306
  let description: UnsafePointer<UInt8>?
  let size: Size
  let alignment: Alignment
  let type_argument_or_parameter_count: UInt16
}

/// Fatal error unless TypeWitnessHeader lays out in declaration
/// order in Hylo.
func checkLayoutRequirements() {
  precondition(
    MemoryLayout<StringPointer>.alignment >= MemoryLayout<Size>.alignment,
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
  func size() -> Size { self[0].size }

  /// Returns the alignment of an instance
  func alignment() -> UInt16 { self[0].alignment }

}

// ====== Make the code read like disabled Hylo. =======
private extension UnsafePointer {

  func pointee() -> Pointee { self[0] }
  func copy() -> Self { self }

}

private extension UnsafeMutablePointer {

  func pointee() -> Pointee { self[0] }
  mutating func set_pointee(_ x: Pointee) { self[0] = x }
  func copy() -> Self { self }

}

private extension BinaryInteger {

  func copy() -> Self { self }

}
// ===================================================

/// Returns the first element `x` of `start..<end` such that
/// `p(x.pointee())` is true.
private func first_position(
  from start: UnsafeMutablePointer<RecordMemberType>,
  to end: UnsafeMutablePointer<RecordMemberType>,
  where p: (RecordMemberType)->Bool
) -> UnsafeMutablePointer<RecordMemberType> {
  var i = start.copy()
  while i < end && !p(i.pointee()) {
    i += 1
  }
  return i
}

/// Removes the contiguous elements at the tail of `start..<end` whose
/// pointees satisfy `p`.
private func drop_last(
  from start: UnsafeMutablePointer<RecordMemberType>,
  to end: inout UnsafeMutablePointer<RecordMemberType>,
  `while` p: (RecordMemberType)->Bool
) {
  while end != start && p((end - 1).pointee()) {
    end -= 1
  }
}

/// Removes the contiguous elements at the head of `start..<end` whose
/// pointees satisfy `p`.
private func drop(
  from start: inout UnsafeMutablePointer<RecordMemberType>,
  to end: UnsafeMutablePointer<RecordMemberType>,
  `while` p: (RecordMemberType)->Bool
) {
  start = first_position(from: start, to: end, where: { !p($0) })
}

/// Shifts the contents of `start..<end` one position later in memory.
private func shift_backward1(
  from start: UnsafeMutablePointer<RecordMemberType>,
  until end: UnsafeMutablePointer<RecordMemberType>
) {
  var e = end.copy()
  while e != start {
    let e0 = e - 1
    e.set_pointee(e0.pointee())
    e = e0
  }
}

/// Inserts `source.pointee()` at the latest position *q* in
/// `destinationStart...destinationEnd` such that all its
/// predecessors' `pointee`s have `alignment` ≥
/// *q*`.pointee().alignment()`.
///
/// - Precondition: the pointees of
///   `destinationStart..<destinationEnd` are sorted by decreasing
///   alignment.
/// - Precondition: `source >= destinationEnd`.
private func insert_backward_stably_sorted_by_decreasing_alignment(
  into destinationStart: UnsafeMutablePointer<RecordMemberType>,
  until destinationEnd: inout UnsafeMutablePointer<RecordMemberType>,
  from source: UnsafeMutablePointer<RecordMemberType>
) {
  let r = source.pointee()
  let a = r.alignment()

  var i = destinationEnd.copy()
  drop_last(
    from: destinationStart, to: &i, while: { $0.alignment() < a })

  if source != i {
    shift_backward1(from: i, until: destinationEnd)
    i.set_pointee(r)
  }
  destinationEnd += 1
}

/// Inserts the pointees in `sourceStart_..<sourceEnd` that satisfy
/// `p` at the latest position `q` in
/// `destinationStart...destinationEnd` such that all their
/// predecessors' `pointee`s have `alignment` ≥
/// *q*`.pointee().alignment()`.
///
/// - Precondition: the pointees of
///   `destinationStart..<destinationEnd` are sorted by decreasing
///   alignment.
/// - Precondition: `sourceStart_ >= destinationEnd`.
private func insert_backward_stably_sorted_by_decreasing_alignment(
  into destinationStart: UnsafeMutablePointer<RecordMemberType>,
  until destinationEnd: inout UnsafeMutablePointer<RecordMemberType>,
  from sourceStart: consuming UnsafeMutablePointer<RecordMemberType>,
  until sourceEnd: UnsafeMutablePointer<RecordMemberType>,
  where p: (RecordMemberType)->Bool
) {
  while sourceStart != sourceEnd {
    if p(sourceStart.pointee()) {
      insert_backward_stably_sorted_by_decreasing_alignment(
        into: destinationStart, until: &destinationEnd, from: sourceStart)
    }
    sourceStart += 1
  }
}

/// Removes from start..<end the elements with alignments less than
/// that of n, or with the same alignment as n but occurring at a
/// position > n, and stably sorts them by decreasing alignment.
private func filter_and_stable_sort_elements_by_decreasing_alignment(
  from start: inout UnsafeMutablePointer<RecordMemberType>,
  to end: inout UnsafeMutablePointer<RecordMemberType>,
  that_lay_out_before n: UnsafeMutablePointer<RecordMemberType>,
  having_alignment n_alignment: Alignment
) {
  // Drop initial unretained elements before n
  drop(from: &start, to: n, while: { $0.alignment() < n_alignment })

  var new_end: UnsafeMutablePointer<RecordMemberType>
  let tail_start: UnsafeMutablePointer<RecordMemberType>

  if start != n {
    // insert elements up to n
    new_end = start + 1

    insert_backward_stably_sorted_by_decreasing_alignment(
      into: start, until: &new_end, from: start + 1, until: n,
      where: { $0.alignment() >= n_alignment })

    tail_start = n + 1
  }
  else {
    // Drop unretained elements after n
    start = n + 1
    drop(
      from: &start, to: end,
      while: { $0.alignment() <= n_alignment })
    
    if start == end { return }
    
    new_end = start + 1
    tail_start = new_end
  }

  // insert elements after n
  insert_backward_stably_sorted_by_decreasing_alignment(
    into: start, until: &new_end, from: tail_start, until: end,
    where: { $0.alignment() > n_alignment })
  end = new_end
}

/// Returns the size a record type would have were its members given
/// in storage order by `start..<end`.
private func size_of_record_having_ordered_members(
  from start: consuming UnsafePointer<RecordMemberType>,
  to end: UnsafePointer<RecordMemberType>
) -> Size {
  var r = 0 as Size
  while start < end {
    let w = start.pointee()
    let position = w.alignment().first_aligned_offset(starting_from: r)
    r = position + w.size()
    start += 1
  }
  return r
}

/// Returns the offset of the `n`th member in declaration order of a
/// record type having members given by the array of length `l` at
/// `memberArray`.
///
/// Mutates the elements in the array in arbitrary ways.
private func __hylo_offset_of_member(
  _ n: UInt32,
  in memberArray: UnsafeMutablePointer<RecordMemberType>, of_length l: UInt32) -> UInt32
{
  let p = memberArray + Int(n)
  let nth_alignment = p.pointee().alignment()
  var start = memberArray
  var end = memberArray + Int(l)

  filter_and_stable_sort_elements_by_decreasing_alignment(
    from: &start, to: &end, that_lay_out_before: p, having_alignment: nth_alignment)
  if start == end { return 0 }
  let preceding_size = size_of_record_having_ordered_members(from: start, to: end)
  return nth_alignment.first_aligned_offset(starting_from: preceding_size)
}

//
// =================== TESTING UTILITIES ===============
//

private struct RecordLayout {
  let start: UnsafeMutablePointer<RecordMemberType>
  let count: UInt32
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

  fileprivate func w(size: Size, alignment: Alignment) -> TypeWitnessHeader {
    .init(
      description: nil,
      size: size, alignment: alignment,
      type_argument_or_parameter_count: 0)
  }

  fileprivate func offsets(members: [(size: Size, alignment: Alignment)]) -> [UInt32] {
    let witnesses = members.map { (s, a) in w(size: s, alignment: a) }
    return witnesses.withUnsafeBufferPointer { headers in
      let witnessPointers = headers.indices.map { headers.baseAddress! + $0 }
      return witnessPointers.indices.map { i in
        var scratch = witnessPointers
        return scratch.withUnsafeMutableBufferPointer { b in
          return __hylo_offset_of_member(
            UInt32(i), in: b.baseAddress!, of_length: UInt32(b.count))
        }
      }
    }
  }

  /// Fragments of the Hylo test input file.
  var hyloTestCases: [String] = []

  /// Returns a the test case formatted for the Hylo test
  /// input file.
  private func hyloTestCase(
    members sas: [(size: Size, alignment: Alignment)],
    offsets os: [UInt32]
  ) -> String {
    func field<T>(_ x: T, width: Int) -> String {
      let s = "\(x)"
      return s + repeatElement(" ", count: max(0, width - s.count))
    }

    let sas1 = sas + repeatElement((size: 0, alignment: 0), count: 10 - sas.count)
    let os1 = os + repeatElement(0, count: 10 - os.count)

    return """
      \(sas1.map { sa in "\(sa.size) \(sa.alignment)  " }.joined())
      \(os1.map { field($0, width: 4) }.joined(separator: " "))
      """
  }

  /// Returns the contents of the Hylo test file.
  private func writeHyloTestFile() throws {
    try (hyloTestCases.joined(separator: "\n") + "\n-1\n")
      .write(toFile: "test-cases.txt", atomically: true, encoding: .utf8)
  }

  private func checkOffsets(members sa: [(size: Size, alignment: Alignment)]) {
    if sa.count == 0 { return }
    let offsets = offsets(members: sa)
    // hyloTestCases.append(hyloTestCase(members: sa, offsets: offsets))

    let memberOrder = sa.indices.sorted { (i, j) in
      offsets[i] < offsets[j]
        || offsets[i] == offsets[j] && sa[i].alignment > sa[j].alignment
    }

    // First member always sits at offset 0
    XCTAssertEqual(offsets[memberOrder.first!], 0)
    for (i0, i1) in zip(memberOrder, memberOrder.dropFirst()) {
      let (m0, o0) = (sa[i0], offsets[i0])
      let (m1, o1) = (sa[i1], offsets[i1])
      XCTAssertGreaterThanOrEqual(
        m0.alignment, m1.alignment,
        """
        Member \(i0) with alignment \(m0.alignment) ordered before member \(i1) 
          with alignment \(m1.alignment) !
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )
      if m0.alignment == m1.alignment {
        XCTAssertLessThan(
          i0, i1,
          """
          Members \(i0) and \(i1) with the same alignment are out of order!
          \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
          """
        )

      }
      XCTAssertGreaterThanOrEqual(
        m0.alignment, m1.alignment,
        """
        Increasing alignment between consecutive members \(i0) and \(i1)!
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )

      XCTAssert(
        o1 % UInt32(m1.alignment) == 0,
        """
          member \(i1) at offset \(o1) not aligned to \(m1.alignment)!
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )

      let end0 = o0 + m0.size
      XCTAssertLessThanOrEqual(
        end0, o1,
        """
        member \(i1) at offset \(o1) overlaps preceding member \(i0) at \(o0)!
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """
      )
      let padding = o1 &- end0

      XCTAssertLessThanOrEqual(
        padding, UInt32(m1.alignment),
        """
        Needless padding \(padding) before member at offset \(o1)
        \(zip(sa, offsets).map {"\n\($0), offset: \($1)"}.joined())
        """)
    }
  }

  func pathToThisFile(p: String = #filePath) -> String { p }

  func testOffsetOfMember() throws {

    let testDataFile = URL(filePath: pathToThisFile())
      .deletingLastPathComponent()
      .deletingLastPathComponent()
      .appending(
        path: "CompilerTests/positive/runtime-offset-of-member.package/test-cases.txt")

    var input = try String(contentsOf: testDataFile, encoding: .utf8)[...]

    func read1() -> Int? {
      let i = input.drop { $0.isWhitespace }
      let s = i.prefix { !$0.isWhitespace }
      if let r = Int(s) {
        input = input[s.endIndex...]
        return r
      }
      return nil
    }

    func read(_ n: Int) -> [Int] {
      var r: [Int] = []
      for _ in 0..<n {
        guard let i = read1() else { break }
        r.append(i)
      }
      return r
    }

    var testCount = 0
    while !input.isEmpty {
      guard let first = read1() else {
        fatalError("invalid test file format; missing next line")
      }
      if first == -1 { break }
      let m = [first] + read(19)
      if m.count != 20 { fatalError("incomplete case line of length \(m.count)") }
      let memberCount = (0..<10).first { m[$0 * 2 + 1] == 0 } ?? 10
      let p = (0..<memberCount).map {
        (size: Size(m[$0 * 2]), alignment: Alignment(m[$0 * 2 + 1]))
      }
      checkOffsets(members: p)

      let x = read(10)
      if x.count != 10 {
        fatalError("incomplete expectations of length \(x.count)")
      }
      testCount += 1
    }
    XCTAssertGreaterThan(testCount, 100, "Not much testing happened")
  }

}

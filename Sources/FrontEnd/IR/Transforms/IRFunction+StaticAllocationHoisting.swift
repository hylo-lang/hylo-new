import Utilities

extension IRFunction {

  /// Moves all static stack allocations to the entry block, updating all usages.
  internal mutating func hoistStackAllocationsToEntryBlock() {
    guard let entry else { return }

    let n = instructions().count
    let ss = replicateAllocations(to: entry)
    substituteValues(ss)

    // Remove all old instructions that are now obsolete.
    for v in ss.values.keys {
      remove(v.register ?? unreachable("Expected values shall originate from `IRAlloca`."))
    }

    assert(n == instructions().count, "The transformation shall preserve instruction count.")
    assertNoAllocasOutsideEntry()
  }

  /// Asserts that no IRAlloca instructions exist outside the entry block.
  private func assertNoAllocasOutsideEntry() {
    #if DEBUG
    for b in blocks.addresses.dropFirst() {
      for i in instructions(in: b) {
        assert(!(at(i) is IRAlloca), "IRAlloca shall only appear in the entry block.")
      }
    }
    #endif
  }

  /// Replicates all static allocations from outside of the entry block to the given (entry) block.
  private mutating func replicateAllocations(to e: IRBlock.ID) -> IRSubstitutionTable {
    var ss = IRSubstitutionTable()

    for b in blocks.addresses.dropFirst().reversed() {
      for i in instructions(in: b) {
        if let a = at(i) as? IRAlloca {
          // It doesn't matter where we insert it within the entry block, so we just insert it at
          // the start because that's always there. We do the iteration in reverse order to preserve
          // sanity, but it's not significant.
          ss[IRValue.register(i)] = .register(insert(a, at: .start(of: e)))
        }
      }
    }

    return ss
  }

}



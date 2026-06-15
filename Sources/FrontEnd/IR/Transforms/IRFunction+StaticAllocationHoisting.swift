import Utilities

extension IRFunction {

  /// Moves all static stack allocations to the entry block, updating all usages.
  internal mutating func hoistStackAllocationsToEntryBlock() {
    guard let entry else { return }

    let n = instructions().count
    
    for b in blocks.addresses.dropFirst().reversed() {
      for i in instructions(in: b) {
        if tag(of: i) == IRAlloca.self {
          relinkToStart(i)
        }
      }
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

}



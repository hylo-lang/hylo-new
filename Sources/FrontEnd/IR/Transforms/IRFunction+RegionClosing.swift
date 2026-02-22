import Utilities

extension IRFunction {

  /// Adds missing closing instructions after the last uses of region opening definitions.
  ///
  /// Some instructions (e.g., `access`) define a value and open non-lexical region in which that
  /// value is considered alive. In the final IR, each opened region must be closed by an `end`
  /// instruction after the last use of the corresponding definition, on all execution paths. This
  /// IR pass guarantees that invariant.
  ///
  /// This pass expects to run after dead access elimination.
  internal mutating func closeOpenEndedRegions() {
    let g = controlFlow()
    for i in instructions() {
      switch tag(of: i) {
      case IRAccess.self:
        close(IRAccess.self, i, computingLivenessWith: g)
      case IRProject.self:
        close(IRProject.self, i, computingLivenessWith: g)
      default:
        continue
      }
    }
  }

  /// Closes the region opened by `i`, which is an instance of `T`, iff `i` it is open-ended,
  /// using `g` to compute live ranges.
  private mutating func close<T: IRRegionEntry>(
    _: T.Type, _ i: AnyInstructionIdentity, computingLivenessWith g: ControlFlowGraph
  ) {
    let r = extendedLiveRange(of: .register(i), controlFlow: g)
    for boundary in r.upperBoundaries {
      switch boundary {
      case .after(let u):
        // Skip the insertion if the last user already closes the borrow.
        if let e = at(u) as? IRRegionEnd<T>, e.start.register == i {
          continue
        }
        let a = at(u).anchor
        insert(IRRegionEnd<T>(start: .register(i), anchor: a), after: u)

      case .start(let b):
        let a = blocks[b].first.map({ (s) in at(s).anchor }) ?? at(i).anchor
        insert(IRRegionEnd<T>(start: .register(i), anchor: a), at: boundary)

      default:
        unreachable()
      }
    }
  }

  /// Returns the extended live-range of `v`, which is a definition.
  ///
  /// A definition is *live* over an instruction if it is is used by that instruction or may be
  /// used by another instruction in the future. The live-range of a definition `d` is the region
  /// of a function containing all instructions over which `d` is live. The extended live-range of
  /// `d` is its live-range merged with the extended live-ranges of the definitions extending `d`.
  ///
  /// - Note: The definition of an operand `o` isn't part of `o`'s lifetime.
  private func extendedLiveRange(of v: IRValue, controlFlow g: ControlFlowGraph) -> Lifetime {
    // Nothing to do if the operand has no use.
    guard let uses = self.uses[v] else { return Lifetime(operand: v) }

    // Nothing to do if the operand isn't a definition.
    guard let b = block(defining: v) else { return Lifetime(operand: v) }

    // Compute the live-range of the definition and extend it with that of its extending uses.
    var r = liveRange(of: v, definedIn: b, controlFlow: g)
    for use in uses where at(use.user).isExtendingOperandLifetimes {
      r = extended(r, toCover: extendedLiveRange(of: .register(use.user), controlFlow: g))
    }

    return r
  }

  /// Returns the minimal lifetime containing all instructions using `v`, which is defined in basic
  /// block `b` contained in control-flow graph `g`.
  private func liveRange(
    of operand: IRValue, definedIn b: IRBlock.ID, controlFlow g: ControlFlowGraph
  ) -> Lifetime {

    // This implementation is a variant of Appel's path exploration algorithm found in Brandner et
    // al.'s "Computing Liveness Sets for SSA-Form Programs".

    // Find all blocks in which the operand is being used.
    var occurrences = uses[operand, default: []].reduce(into: Set<IRBlock.ID>()) { (bs, use) in
      bs.insert(block(defining: use.user))
    }

    // Propagate liveness starting from the blocks in which the operand is being used.
    var approximation: [IRBlock.ID: (liveIn: Bool, liveOut: Bool)] = [:]
    while true {
      guard let occurrence = occurrences.popFirst() else { break }

      // `occurrence` is the defining block.
      if b == occurrence { continue }

      // We already propagated liveness to the block's live-in set.
      if approximation[occurrence]?.liveIn ?? false { continue }

      // Mark that the definition is live at the block's entry and propagate to its predecessors.
      approximation[occurrence, default: (false, false)].liveIn = true
      for predecessor in g.predecessors(of: occurrence) {
        approximation[predecessor, default: (false, false)].liveOut = true
        occurrences.insert(predecessor)
      }
    }

    var coverage: Lifetime.Coverage = [:]

    // If the operand isn't live out of its defining block, its last use is in that block.
    if approximation.isEmpty {
      coverage[b] = .closed(lastUse: lastUse(of: operand, in: b))
      return Lifetime(operand: operand, coverage: coverage)
    }

    // Find the last use in each block for which the operand is not live out.
    var successors: IRBlockSet = []
    for (block, bounds) in approximation {
      switch bounds {
      case (true, true):
        coverage[block] = .liveInAndOut
        successors.formUnion(g.successors(of: block))
      case (false, true):
        coverage[block] = .liveOut
        successors.formUnion(g.successors(of: block))
      case (true, false):
        coverage[block] = .liveIn(lastUse: lastUse(of: operand, in: block))
      case (false, false):
        continue
      }
    }

    // Mark successors of live out blocks as live in if they haven't been already.
    for block in decode(successors) where coverage[block] == nil {
      coverage[block] = .liveIn(lastUse: nil)
    }

    return Lifetime(operand: operand, coverage: coverage)
  }

  /// Returns `lhs` extended to cover the instructions in `rhs`.
  ///
  /// - Requires: `lhs` and `rhs` are defined in the same function, which is in `self`. The operand
  ///   for which `rhs` is defined must be in `lhs`.
  private func extended(_ lhs: Lifetime, toCover rhs: Lifetime) -> Lifetime {
    let coverage = lhs.coverage.merging(rhs.coverage) { (x, y) in
      switch (x, y) {
      case (.liveOut, .liveIn), (.liveIn, .liveOut):
        fatalError("definition does not dominate all uses")
      case (.liveInAndOut, _), (_, .liveInAndOut):
        return .liveInAndOut
      case (.liveOut, _), (_, .liveOut):
        return .liveOut
      case (.liveIn(let a), .liveIn(let b)):
        return .liveIn(lastUse: sequencedLast(a, b))
      case (.liveIn(let a), .closed(let b)):
        return .liveIn(lastUse: sequencedLast(a, b))
      case (.closed(let a), .liveIn(let b)):
        return .liveIn(lastUse: sequencedLast(a, b))
      case (.closed(let a), .closed(let b)):
        return .closed(lastUse: sequencedLast(a, b))
      }
    }
    return .init(operand: lhs.operand, coverage: coverage)
  }

  /// Returns the use that executes last iff `lhs` and `rhs` are in the same basic block.
  private func sequencedLast(_ lhs: Use?, _ rhs: Use?) -> Use? {
    guard let a = lhs else { return rhs }
    guard let b = rhs else { return lhs }

    if a.user == b.user {
      return a.index < b.index ? rhs : lhs
    } else {
      return instructions(after: a.user).contains(b.user) ? rhs : lhs
    }
  }

}

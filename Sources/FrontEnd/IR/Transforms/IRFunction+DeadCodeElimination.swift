import Utilities

extension IRFunction {

  /// Removes the code after calls returning `Never`.
  ///
  /// This method only removes instructions that are in the same basic block as a never-returning
  /// call, or that are users of a removed instruction. Some basic blocks in `self` may become
  /// unreachable as a result of the transformation, but no basic block is removed.
  internal mutating func removeCodeAfterNeverReturningCalls() {
    for b in blocks.addresses {
      if let i = instructions(in: b).first(where: neverReturns(_:)) {
        removeWithUsers(instructions(after: i))

        let a = at(i).anchor
        let s = IRUnreachable(anchor: a.emptyAtEnd)
        append(s, to: b)
      }
    }
  }

  /// Removes the basic blocks that have no predecessor.
  internal mutating func removeUnreachableBlocks() {
    // Nothing to do if the function has no definition.
    if !isDefined { return }

    var cfg = controlFlow()
    var work = blocks.addresses.filter({ (b) in isUnreachable(b, in: cfg) })

    // `work` acts as a stack containing the basic blocks that should be eventually removed. At
    // each iteration, we can either remove a block or grow the stack with successors that have
    // to be removed first. The algorithm terminates because the stack can only grow after having
    // removed relations from the control flow graph; otherwise it is popped.
    while let a = work.last {
      // `a` can be remove if it has no outgoing edges. Note that we may get here after `a` has
      // already been visited once.
      if cfg.successors(of: a).isEmpty {
        removeBlock(a)
        work.removeLast()
      }

      // If `a` has successors `b`, then `a` can be removed if all these these successors have at
      // least one other predecessors. In this case, `a` is not a dominator and therefore it cannot
      // contain definitions used elsewhere. Otherwise, all successors dominated that are dominated
      // by `a` must be removed first.
      else {
        for b in successors(of: a) {
          cfg.remove(a, fromPredecessorsOf: b)
          if isUnreachable(b, in: cfg) { work.append(b) }
        }
      }
    }
  }

  /// Removes the instructions that have no user and no observable run-time effect.
  internal mutating func removedUnusedDefinitions() {
    var work = Array(instructions())
    var done: Set<AnyInstructionIdentity> = []
    while let i = work.popLast() {
      if done.contains(i) { continue }
      if uses[.register(i), default: []].isEmpty && isRemovableWhenUnused(i) {
        work.append(contentsOf: at(i).operands.compactMap(\.register))
        done.insert(i)
        remove(i)
      }
    }
  }

  /// Returns `true` iff `b` is unreachable from the function's entry.
  private func isUnreachable(_ b: IRBlock.ID, in cfg: ControlFlowGraph) -> Bool {
    (b != entry) && cfg.predecessors(of: b).isEmpty
  }

  /// Returns `true` iff `i` can be removed if it has no use.
  private func isRemovableWhenUnused(_ i: AnyInstructionIdentity) -> Bool {
    switch at(i) {
    case let s as IRApplyBuiltin:
      return s.callee != .trap
    case let s:
      return s.type != .nothing
    }
  }

  /// Returns `true` iff `i` denotes an instruction that never returns control.
  ///
  /// `Never` is encoded as `<T> T`, meaning that a never-returning expression will typically be
  /// wrapped into a type application so that it matches the expected type. This method can thus
  /// identify the instruction denoting the lowered form of a never-returning expression right
  /// before any type application.
  private func neverReturns(_ i: AnyInstructionIdentity) -> Bool {
    // Note that it's fine to compare the return type of applications with `Never` because the
    // expression should still have the form `<T> T` at this point.
    switch at(i) {
    case let s as IRApply:
      return result(of: s.result)?.type == .never
    case let s as IRApplyBuiltin:
      return s.callee == .trap
    default:
      return false
    }
  }

}

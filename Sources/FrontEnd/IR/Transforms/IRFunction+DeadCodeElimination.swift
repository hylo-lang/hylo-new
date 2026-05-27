import Utilities

extension IRFunction {

  /// Removes the code after calls returning `Never`.
  internal mutating func removeCodeAfterCallsReturning(never: AnyTypeIdentity) {
    for b in blocks.addresses {
      if let i = instructions(in: b).first(where: { (i) in returns(never: never, i) }) {
        removeAll(after: i)

        let a = at(i).anchor
        let s = IRUnreachable(anchor: .init(site: .empty(at: a.site.end), scope: a.scope))
        append(s, to: b)
      }
    }
  }

  /// Removes the basic blocks that have no predecessor.
  internal mutating func removeUnreachableBlocks() {
    // Nothing to do if the function has no definition.
    guard let e = entry else { return }

    /// Returns `true` iff `b` is unreachable from the function's entry.
    func isUnreachable(_ b: IRBlock.ID, in cfg: ControlFlowGraph) -> Bool {
      (b != e) && cfg.predecessors(of: b).isEmpty
    }

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

  /// Returns `true` iff `i` can be removed if it has no use.
  private func isRemovableWhenUnused(_ i: AnyInstructionIdentity) -> Bool {
    switch at(i) {
    case let s:
      return s.type != .nothing
    }
  }

  /// Returns `true` iff `i` denotes an instruction that never returns control.
  ///
  /// `Never` is encoded as `<T> T`, meaning that a never-returning expression will typically be
  /// wrapped into a type application so that the it matches the expected type. This method can
  /// therefore identify the instruction denoting the lowered form of a never-returning expression
  /// right before any type application.
  private func returns(never: AnyTypeIdentity, _ i: AnyInstructionIdentity) -> Bool {
    // Note that it's fine to compare the return type of applications with `Never` because the
    // expression should still have the form `<T> T` at this point.
    switch at(i) {
    case let s as IRApply:
      return result(of: s.result)?.type == never
    default:
      return false
    }
  }

}

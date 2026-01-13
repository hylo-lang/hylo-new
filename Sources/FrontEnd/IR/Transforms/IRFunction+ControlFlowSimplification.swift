extension IRFunction {

  /// Eliminates needless basic blocks to simplify the control-flow graph of the function.
  internal mutating func simplifyControlFlow() {
    // Nothing to do if there isn't more than one basic block.
    if blocks.count <= 1 { return }

    var g = controlFlow()
    var work = Array(blocks.addresses)

    while let b = work.popLast() {
      // Remove blocks whose only instruction is an unconditional branch.
      if let i = uniqueInstruction(in: b).flatMap({ (i) in cast(i, to: IRBranch.self) }) {
        let t = at(i).target

        let ps = Array(g.predecessors(of: b))
        for p in ps {
          g.define(p, predecessorOf: t)
          g.remove(p, fromPredecessorsOf: b)
          _ = replaceSuccessor(b, of: p, for: t)
        }

        let ss = Array(g.successors(of: b))
        for s in ss {
          g.remove(b, fromPredecessorsOf: s)
        }

        removeBlock(b)
      }

      // Can we merge `b` into its predecessor?
      else if let p = g.predecessors(of: b).uniqueElement, successors(of: p).count == 1 {
        // TODO
      }
    }
  }

}

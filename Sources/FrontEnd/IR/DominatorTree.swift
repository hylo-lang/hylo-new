import Utilities

/// A tree whose nodes are basic blocks and where a node immediately dominates its children.
///
/// Definitions:
/// - A block `b1` in a control-flow graph *dominates* a block `b2` if every path from the entry to
///   `b2` must go through `b1`. By definition, every node dominates itself.
/// - A block `b1` *strictly dominates* a block `b2` if `b1` dominates `b2` and `b1 != b2`.
/// - A block `b1` *immediately dominates* a block `b2` if `b1` strictly dominates `b2` and there
///   is no block `b3` that strictly dominates `b2`.
///
/// A dominator tree encodes the dominance relation of a control graph as a tree where a node is
/// a basic blocks and its children are those it immediately dominates.
internal struct DominatorTree: Sendable {

  /// The root of the tree.
  internal let root: IRBlock.ID

  /// The immediate dominators of each basic block.
  private var immediateDominators: [IRBlock.ID: IRBlock.ID?]

  /// Creates the dominator tree of `f` using its control-flow graph `g`.
  internal init(function f: IRFunction, controlFlow g: ControlFlowGraph) {
    // The following is an implementation of Cooper et al.'s fast dominance iterative algorithm
    // (see "A Simple, Fast Dominance Algorithm", 2001). First, build any spanning tree rooted at
    // the function's entry.
    var t = g.spanningTree(rootedAt: f.entry!)

    // Then, until a fixed point is reached, for each block `v` that has a predecessor `u` that
    // isn't `v`'s parent in the tree, assign `v`'s parent to the least common ancestor of `u` and
    // its current parent.
    var changed = true
    while changed {
      changed = false
      for v in f.blocks.addresses {
        for u in g.predecessors(of: v) where t.parent(v) != u {
          let lca = t.lowestCommonAncestor(u, t.parent(v)!)
          if lca != t.parent(v) {
            t.setParent(lca, forChild: v)
            changed = true
          }
        }
      }
    }

    // The resulting tree encodes the immediate dominators.
    root = f.entry!
    immediateDominators = t.parents
  }

  /// A collection containing the blocks in this tree in breadth-first order.
  internal var bfs: [IRBlock.ID] {
    let children: [IRBlock.ID: [IRBlock.ID]] = immediateDominators.reduce(into: [:]) { (cs, kv) in
      if case .some(let parent) = kv.value {
        cs[parent, default: []].append(kv.key)
      }
    }

    var result = [root]
    var i = 0
    while i < result.count {
      if let nodes = children[result[i]] { result.append(contentsOf: nodes) }
      i += 1
    }
    return result
  }

  /// Returns the immediate dominator of `b`, if any.
  internal func immediateDominator(of b: IRBlock.ID) -> IRBlock.ID? {
    if case .some(.some(let d)) = immediateDominators[b] {
      return d
    } else {
      return nil
    }
  }

  /// Returns a collection containing the strict dominators of `b`.
  internal func strictDominators(of b: IRBlock.ID) -> [IRBlock.ID] {
    var result: [IRBlock.ID] = []
    var a = b
    while let d = immediateDominator(of: a) {
      result.append(d)
      a = d
    }
    return result
  }

  /// Returns `true` if `a` dominates `b`.
  internal func dominates(_ a: IRBlock.ID, _ b: IRBlock.ID) -> Bool {
    // By definition, a node dominates itself.
    if a == b { return true }

    // Walk the dominator tree from `b` up to the root to find `a`.
    var child = b
    while let parent = immediateDominator(of: child) {
      if parent == a { return true }
      child = parent
    }
    return false
  }

  /// Returns `true` if the instruction identified by `definition` dominates `use` in `self`, which
  /// is the dominator tree of `f`.
  internal func dominates(definition: AnyInstructionIdentity, use: Use, in f: IRFunction) -> Bool {
    let a = f.block(defining: definition)
    let b = f.block(defining: use.user)

    // If both instructions are in the same block, determine which comes first. Otherwise, use the
    // relation encoded in the tree.
    if a == b {
      return f.precedes(definition, use.user)
    } else {
      return dominates(a, b)
    }
  }

}

extension DominatorTree: CustomStringConvertible {

  /// The Graphviz (dot) representation of the tree.
  internal var description: String {
    var result = "strict digraph D {\n\n"
    for (a, d) in immediateDominators {
      if let b = d {
        result.write("\(a) -> \(b);\n")
      } else {
        result.write("\(a);\n")
      }
    }
    result.write("\n}")
    return result
  }

}

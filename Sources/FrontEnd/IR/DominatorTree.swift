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
public struct DominatorTree: Sendable {

  /// The root of the tree.
  public let root: IRBlock.ID

  /// The immediate dominators of each basic block.
  private var immediateDominators: [IRBlock.ID: IRBlock.ID?]

  /// Creates the dominator tree of `g`, which is a subgraph of the control-flow graph of `f`
  /// rooted at `r`.
  public init(function f: IRFunction, controlFlow g: ControlFlowGraph, rootedAt r: IRBlock.ID) {
    // The following is an implementation of Cooper et al.'s fast dominance iterative algorithm
    // (see "A Simple, Fast Dominance Algorithm", 2001). First, build any spanning tree from the
    // given root (typically the function's entry).
    var t = g.spanningTree(rootedAt: r)

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
    root = r
    immediateDominators = t.parents
  }

  /// Creates the dominator tree of `g`, which is the control-flow graph of `f`.
  public init(function f: IRFunction, controlFlow g: ControlFlowGraph) {
    self.init(function: f, controlFlow: g, rootedAt: f.entry!)
  }

  /// A collection containing the blocks in this tree in breadth-first order.
  public var bfs: [IRBlock.ID] {
    let cs = children()

    var result = [root]
    var i = 0
    while i < result.count {
      if let nodes = cs[result[i]] { result.append(contentsOf: nodes) }
      i += 1
    }
    return result
  }

  /// Returns a mapping from a node to the blocks that it immediately dominates.
  public func children() -> [IRBlock.ID: SortedSet<IRBlock.ID>] {
    immediateDominators.reduce(into: [:]) { (cs, kv) in
      if case .some(let parent) = kv.value {
        cs[parent, default: []].insert(kv.key)
      }
    }
  }

  /// Returns the immediate dominator of `b`, if any.
  public func immediateDominator(of b: IRBlock.ID) -> IRBlock.ID? {
    if case .some(.some(let d)) = immediateDominators[b] {
      return d
    } else {
      return nil
    }
  }

  /// Returns a sequence with the dominators of `b`, ordered such that each element is immediately
  /// dominated by its successor and including `b` itself iff `strict` is `true`.
  ///
  /// The returned sequence starts with `b` iff `strict` is `false`. Otherwise, the first element
  /// of the sequence is the immediate dominator of `b`, if any.
  public func dominators(of b: IRBlock.ID, strict: Bool = false) -> [IRBlock.ID] {
    var result: [IRBlock.ID] = strict ? [] : [b]
    var a = b
    while let d = immediateDominator(of: a) {
      result.append(d)
      a = d
    }
    return result
  }

  /// Returns `true` if `a` dominates `b`.
  public func dominates(_ a: IRBlock.ID, _ b: IRBlock.ID) -> Bool {
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

  /// Returns `true` iff `a` strictly dominates `b`.
  public func strictlyDominates(_ a: IRBlock.ID, _ b: IRBlock.ID) -> Bool {
    (a != b) && dominates(a, b)
  }

  /// Returns `true` if the instruction identified by `definition` dominates `use` in `self`, which
  /// is the dominator tree of `f`.
  public func dominates(definition: AnyInstructionIdentity, use: Use, in f: IRFunction) -> Bool {
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

  /// Returns an iterator over the the basic blocks dominated by `b`.
  public func region(dominatedBy b: IRBlock.ID) -> DominatorTree.Iterator {
    .init(self, root: b)
  }

}

extension DominatorTree: Sequence {

  /// An iterator over the contents of a dominator tree producing sequences such that the `i`-th
  /// element cannot be dominated by the `j`-th element if `j` is greater than `i`.
  public struct Iterator: IteratorProtocol {

    public typealias Element = IRBlock.ID

    /// The dominator tree being iterated over.
    private let children: [IRBlock.ID: SortedSet<IRBlock.ID>]

    /// A stack with the nodes left to visit.
    private var work: [IRBlock.ID]

    /// Creates an iterator over the subtree of `tree` rooted at `root`.
    public init(_ tree: DominatorTree, root: IRBlock.ID) {
      self.children = tree.children()
      self.work = [root]
    }

    /// Returns the next element, if any.
    ///
    /// - Postcondition: the result, if any, is not dominated by any of the other basic blocks
    ///   generated by `self` so far.
    public mutating func next() -> IRBlock.ID? {
      if let b = work.popLast() {
        work.append(contentsOf: children[b] ?? [])
        return b
      } else {
        return nil
      }
    }

  }

  /// Returns an iterator over the basic blocks in `self`.
  public func makeIterator() -> Iterator {
    .init(self, root: root)
  }

}

extension DominatorTree: CustomStringConvertible {

  /// The Graphviz (dot) representation of the tree.
  public var description: String {
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

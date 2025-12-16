extension ControlFlowGraph {

  /// A spanning tree of a control flow graph.
  internal struct SpanningTree {

    /// A map from node to its parent.
    private(set) var parents: [IRBlock.ID: IRBlock.ID?]

    /// Creates a spanning tree of `g`.
    internal init(of g: ControlFlowGraph, rootedAt root: IRBlock.ID) {
      parents = [:]
      var work: [(vertex: IRBlock.ID, parent: IRBlock.ID??)] = [(root, .some(nil))]
      while let (v, parent) = work.popLast() {
        parents[v] = parent
        let children = g.successors(of: v).filter({ parents[$0] == nil })
        work.append(contentsOf: children.map({ ($0, .some(v)) }))
      }
    }

    /// Returns the parent of `v`.
    ///
    /// - Requires: `v` is in the tree.
    /// - Complexity: O(1).
    internal func parent(_ v: IRBlock.ID) -> IRBlock.ID? {
      parents[v]!
    }

    /// Sets `newParent` as `v`'s parent.
    ///
    /// - Requires: `v` and `newParent` are in the tree and distinct; `v` isn't the root.
    /// - Complexity: O(1).
    internal mutating func setParent(_ newParent: IRBlock.ID, forChild v: IRBlock.ID) {
      parents[v] = .some(newParent)
    }

    /// Returns collection containing `v` followed by all its ancestor, ordered by depth.
    ///
    /// - Requires: `v` is in the tree.
    /// - Complexity: O(*h*) where *h* is the height of `self`.
    internal func ancestors(_ v: IRBlock.ID) -> [IRBlock.ID] {
      var result = [v]
      while let parent = parents[result.last!]! { result.append(parent) }
      return result
    }

    /// Returns the deepest vertex that is ancestor of both `v` and `u`.
    ///
    /// - Requires: `v` and `u` are in the tree.
    /// - Complexity: O(*h*) where *h* is the height of `self`.
    internal func lowestCommonAncestor(_ v: IRBlock.ID, _ u: IRBlock.ID) -> IRBlock.ID {
      var x = ancestors(v)[...]
      var y = ancestors(u)[...]
      while x.count > y.count {
        x.removeFirst()
      }
      while y.count > x.count {
        y.removeFirst()
      }
      while x.first != y.first {
        x.removeFirst()
        y.removeFirst()
      }
      return x.first!
    }

  }

}

extension ControlFlowGraph {

  /// Returns a spanning tree of `self` rooted at `root`.
  internal func spanningTree(rootedAt root: IRBlock.ID) -> SpanningTree {
    SpanningTree(of: self, rootedAt: root)
  }

}

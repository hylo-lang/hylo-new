import Utilities

/// A control-flow graph.
///
/// This data structure describes relation between the basic blocks of a function. The direction of
/// the graph's edges denotes the direction of the control flow from one block to another: there an
/// edge from `A` to `B` if the former's terminator points to the latter.
public struct ControlFlowGraph: Sendable {

  /// An control edge label.
  internal enum Label: Sendable {

    /// A label denoting that the source is a predecessor of the target.
    case forward

    /// A label denoting that the source is a successor of the target.
    case backward

    /// A label denoting that the source is both a predecessor and successor of the target.
    case bidirectional

  }

  /// The way a control-flow relation is represented internally.
  private typealias Relation = DirectedGraph<IRBlock.ID, Label>

  /// The relation encoded by the graph.
  private var relation: Relation

  /// Creates an empty control flow graph.
  internal init() {
    relation = DirectedGraph()
  }

  /// Defines `source` as a predecessor of `target`.
  internal mutating func define(_ source: IRBlock.ID, predecessorOf target: IRBlock.ID) {
    let (inserted, label) = relation.insertEdge(from: source, to: target, labeledBy: .forward)
    if inserted {
      relation[from: target, to: source] = .backward
    } else if label == .backward {
      relation[from: source, to: target] = .bidirectional
      relation[from: target, to: source] = .bidirectional
    }
  }

  /// Removes `source` from the predecessors of `target`.
  internal mutating func remove(_ source: IRBlock.ID, fromPredecessorsOf target: IRBlock.ID) {
    switch relation[from: source, to: target] {
    case .forward:
      relation[from: source, to: target] = nil
      relation[from: target, to: source] = nil
    case .bidirectional:
      relation[from: source, to: target] = .backward
      relation[from: target, to: source] = .forward
    default:
      break
    }
  }

  /// Returns the successors of `source`.
  internal func successors(of source: IRBlock.ID) -> [IRBlock.ID] {
    relation[from: source].compactMap { (tip) in
      tip.value != .backward ? tip.key : nil
    }
  }

  /// Returns the predecessors of `target`.
  internal func predecessors(of target: IRBlock.ID) -> [IRBlock.ID] {
    relation[from: target].compactMap { (tip) in
      tip.value != .forward ? tip.key : nil
    }
  }

  /// A collection where the vertex at index `i + 1` is predecessor of the vertex at index `i`.
  internal typealias PredecessorPath = [IRBlock.ID]

}

extension ControlFlowGraph: CustomStringConvertible {

  /// The Graphviz (dot) representation of the graph.
  public var description: String {
    var result = "strict digraph CFG {\n\n"
    for e in relation.edges {
      switch e.label {
      case .forward:
        result.write("\(e.source) -> \(e.target);\n")
      case .bidirectional:
        result.write("\(e.source) -> \(e.target);\n")
        result.write("\(e.target) -> \(e.source);\n")
      case .backward:
        continue
      }
    }
    result.write("\n}")
    return result
  }

}

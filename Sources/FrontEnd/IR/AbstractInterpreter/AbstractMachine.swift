import Algorithms
import DequeModule

/// A type representing the possible values of an object in an abstract interpreter.
///
/// The values of an abstract domain must form a meet-semilattice whose meet operation represents
/// the conservative superposition of two abstract values.
internal protocol AbstractDomain: Hashable, Sendable {

  /// Returns `lhs` merged with `rhs`.
  static func && (l: Self, r: Self) -> Self

}

/// A function computing the effect of an IR instruction on the state of an abstract machine.
internal protocol AbstractTransferFunction {

  /// The domain of the values in the contexts transformed by this function.
  associatedtype Domain: AbstractDomain

  /// Applies this function on each instruction in `b` of `f` to update the context `c`.
  mutating func apply(
    _ b: IRBlock.ID, from f: inout IRFunction, in c: inout AbstractContext<Domain>,
    using typer: inout Typer
  ) -> Void

}

extension AbstractTransferFunction {

  /// The context in which an instance of `Self` interprets instructions.
  internal typealias Context = AbstractContext<Domain>

}

/// A machine controlling the abstraction interpretation of an IR function.
internal struct AbstractMachine<Interpret: AbstractTransferFunction> {

  /// The knowledge of the abstract interpreter about a single block.
  private typealias BlockState = (
    sources: [IRBlock.ID], pre: Interpret.Context, post: Interpret.Context)

  /// A map from basic block to the machine's state before and after the block's execution.
  private typealias State = [IRBlock.ID: BlockState]

  /// The transfer function that is used to interpret the function.
  private var interpret: Interpret

  /// The control flow graph of the function.
  private var cfg: ControlFlowGraph

  /// The dominator tree of the function.
  private var dominance: DominatorTree

  /// The state of the abstract interpreter before and after the each visited block.
  private var state: State = [:]

  /// A FILO list of blocks to visit.
  private var work: Deque<IRBlock.ID> = []

  /// The set of blocks that no longer need to be visited.
  private var done: IRBlockSet = []

  /// Creates an instance for interpreting `f` with transfer function `interpret`.
  internal init(
    interpreting f: IRFunction, with interpret: Interpret
  ) {
    self.interpret = interpret
    self.cfg = f.controlFlow()
    self.dominance = DominatorTree(function: f, controlFlow: cfg)
  }

  /// Computes a fixed point on the state reached by this machine for each basic block in `f`,
  /// starting from `initialContext` and using `typer` to compute type-related information.
  mutating func fixedPoint(
    of f: inout IRFunction, startingFrom initialContext: Interpret.Context,
    using typer: inout Typer
  ) {
    // Process the entry.
    let entry = dominance.root
    let contextAfterEntry = postContext(
      of: entry, in: &f, startingFrom: initialContext, using: &typer)
    state = [entry: (sources: [], pre: initialContext, contextAfterEntry)]
    done.insert(entry)

    // Enumerate the blocks to visit according to the dominance relation.
    work = Deque(dominance.bfs.dropFirst())

    // Search for a fixed point.
    while let blockToProcess = work.popFirst() {
      guard visitable(blockToProcess) else {
        work.append(blockToProcess)
        continue
      }

      let (sources, before) = preContext(of: blockToProcess)
      let after: Interpret.Context
      let changed: Bool

      // Interpret the block's IR unless we already reached a fixed point.
      if let s = state[blockToProcess], (s.sources == sources) && (s.pre == before) {
        after = s.post
        changed = false
      } else {
        after = postContext(of: blockToProcess, in: &f, startingFrom: before, using: &typer)
        state[blockToProcess] = (sources: sources, pre: before, post: after)
        changed = true
      }

      if !changed && (sources.count == cfg.predecessors(of: blockToProcess).count) {
        done.insert(blockToProcess)
      } else {
        work.append(blockToProcess)
      }
    }
  }

  /// Returns `true` if `b` is ready to be visited.
  ///
  /// Computing the pre-context of `b` requires knowing the state of all uses in `b` that are
  /// defined in its (transitive) predecessors. Because a definition dominates its uses, we can
  /// assume the predecessors dominated by `b` don't define variables used in `b`. Hence, `b` can
  /// be visited iff all its predecessors have been visited or are dominated by `b`.
  private func visitable(_ b: IRBlock.ID) -> Bool {
    if let d = dominance.immediateDominator(of: b) {
      return visited(d)
        && cfg.predecessors(of: b).allSatisfy({ (p) in visited(p) || dominance.dominates(b, p) })
    } else {
      // No predecessor.
      return true
    }
  }

  /// Returns `true` if `b` has been visited.
  private func visited(_ b: IRBlock.ID) -> Bool {
    state[b] != nil
  }

  /// Returns the pre-context of `b` and the predecessors from which it's been computed.
  ///
  /// - Requires: `isVisitable(b)` is `true`
  private func preContext(of b: IRBlock.ID) -> (sources: [IRBlock.ID], pre: Interpret.Context) {
    if b == dominance.root {
      return ([], state[b]!.pre)
    }

    let sources = cfg.predecessors(of: b).filter({ state[$0] != nil })
    return (sources, .init(merging: sources.lazy.map({ state[$0]!.post })))
  }

  /// Returns the post-context of `b` by processing it with `interpret` in `initialContext`.
  private mutating func postContext(
    of b: IRBlock.ID, in f: inout IRFunction, startingFrom initialContext: Interpret.Context,
    using typer: inout Typer
  ) -> Interpret.Context {
    var next = initialContext
    interpret.apply(b, from: &f, in: &next, using: &typer)
    return next
  }

}

import Algorithms
import DequeModule
import Utilities

/// A type representing the possible values of an object in an abstract interpreter.
///
/// The values of an abstract domain must form a meet-semilattice whose meet operation represents
/// the conservative superposition of two abstract values.
internal protocol AbstractDomain: Hashable, Showable, Sendable {

  /// Returns `l` merged with `r`.
  static func && (l: Self, r: Self) -> Self

}

/// A function computing the effect of an IR instruction on the state of an abstract machine.
internal protocol AbstractTransferFunction {

  /// The domain of the values in the contexts transformed by this function.
  associatedtype Domain: AbstractDomain

  /// Applies this function on each instruction in `b` of `f` to update the context `c` and using
  /// `typer` to compute type-related information.
  ///
  /// `c` is the context obtained by merging the contents of `predecessors`, which is a map from
  /// a subset of the predecessors of `b` to their corresponding post-context. This map is only
  /// defined for the basic blocks that have been visited at least once.
  ///
  /// The return value is a set containing the basic blocks that may have been modified during the
  /// application of this method. Those blocks are placed back to the work list of the interpreter
  /// during the computation of a fixed point.
  mutating func apply(
    _ b: IRBlock.ID, from f: inout IRFunction, in c: inout Context,
    precededBy predecessors: SortedDictionary<IRBlock.ID, Context>,
    using typer: inout Typer
  ) -> [IRBlock.ID]

}

extension AbstractTransferFunction {

  /// The context in which an instance of `Self` interprets instructions.
  internal typealias Context = AbstractContext<Domain>

  /// Computes the post-contexts of the basic blocks in `f` until a fixed point is reached using
  /// `typer` to compute type-related information.
  ///
  /// `initialContext` is the context of the abstract interpreter using this method before entering
  /// the entry of the function.
  internal mutating func fixedPoint(
    interpreting f: inout IRFunction, startingFrom initialContext: Context,
    using typer: inout Typer,
  ) {
    var m = AbstractMachine<Self>(interpreting: f)
    m.fixedPoint(interpreting: &f, with: &self, &typer, startingFrom: initialContext)
  }

}

/// A machine controlling the abstraction interpretation of an IR function.
internal struct AbstractMachine<Transfer: AbstractTransferFunction> {

  /// The knowledge of the abstract interpreter about a single block.
  private typealias BlockState = (
    sources: SortedSet<IRBlock.ID>, pre: Transfer.Context, post: Transfer.Context)

  /// A map from basic block to the machine's state before and after the block's execution.
  private typealias State = [IRBlock.ID: BlockState]

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
  fileprivate init(interpreting f: IRFunction) {
    self.cfg = f.controlFlow()
    self.dominance = DominatorTree(function: f, controlFlow: cfg)
  }

  /// Computes a fixed point on the state reached by this machine for each basic block in `f`,
  /// starting from `initialContext`, using `interpret` to interpret IR and `typer` to compute
  /// type-related information.
  fileprivate mutating func fixedPoint(
    interpreting f: inout IRFunction,
    with interpret: inout Transfer, _ typer: inout Typer,
    startingFrom initialContext: Transfer.Context
  ) {
    // Process the entry.
    let entry = dominance.root
    let (contextAfterEntry, _) = postContext(
      of: entry, in: &f, precededBy: [:], mergedInto: initialContext,
      using: &interpret, &typer)

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

      // Did the initial conditions of the block changed since the last time we processed it?
      if let s = state[blockToProcess], s.sources == sources.keys, s.pre == before {
        if sources.count == cfg.predecessors(of: blockToProcess).count {
          done.insert(blockToProcess)
        } else {
          work.append(blockToProcess)
        }
      }

      // If the initial conditions changed, interpret the block.
      else {
        let (after, updated) = postContext(
          of: blockToProcess, in: &f, precededBy: sources, mergedInto: before,
          using: &interpret, &typer)
        state[blockToProcess] = (sources: sources.keys, pre: before, post: after)
        work.append(blockToProcess)

        // `updated` contains the blocks that have been modified by the transfer function and must
        // be re-inserted into the work list, along with their successors.
        var ls: [IRBlock.ID] = []
        for u in updated {
          state[u] = nil
          if done.remove(u) != nil { ls.append(u) }
        }
        while let u = ls.popLast() {
          work.append(u)
          ls.append(contentsOf: cfg.successors(of: u).filter(done.contains(_:)))
        }
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
  private func preContext(
    of b: IRBlock.ID
  ) -> (sources: SortedDictionary<IRBlock.ID, Transfer.Context>, pre: Transfer.Context) {
    assert(b != dominance.root, "entry shouldn't have any predecessor")

    // If no predecessor has been visited yet, just create an empty context.
    let predecessors = cfg.predecessors(of: b)
    guard let i = predecessors.firstIndex(where: { (p) in state[p] != nil }) else {
      return ([:], .init())
    }

    // Otherwise, create a context merging that of all visited predecessor.
    var sources: SortedDictionary = [predecessors[i]: state[predecessors[i]]!.post]
    var context = state[predecessors[i]]!.post
    for p in predecessors[(i + 1)...] {
      guard let s = state[p] else { continue }
      sources[p] = s.post
      context.merge(s.post)
    }

    return (sources, context)
  }

  /// Computes the post-context of `b` using `interpret` to interpret IR and `typer` to compute
  /// type-related information.
  ///
  /// This method is called during the computation of a fixed point to interpret a basic block `b`
  /// using `interpret`, which is the transfer function of the abstract machine. The interpreter is
  /// initialized with `initialContext`, which is the result of merging the post-contexts of the
  /// predecessors of `b` that have been visited, stored in `predecessors`.
  ///
  /// The return value is the post-context of `b` and a set containing the basic blocks that may
  /// have been modified during the application of this method
  private mutating func postContext(
    of b: IRBlock.ID, in f: inout IRFunction,
    precededBy predecessors: SortedDictionary<IRBlock.ID, Transfer.Context>,
    mergedInto initialContext: Transfer.Context,
    using interpret: inout Transfer, _ typer: inout Typer
  ) -> (next: Transfer.Context, updated: [IRBlock.ID]) {
    var next = initialContext
    let updated = interpret.apply(b, from: &f, in: &next, precededBy: predecessors, using: &typer)
    return (next, updated)
  }

}

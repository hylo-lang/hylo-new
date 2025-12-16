import Utilities

/// The evaluation context of an abstract interpreter.
internal struct AbstractContext<Domain: AbstractDomain>: Hashable, Sendable {

  /// The values assigned to registers and parameters.
  internal var locals: [IRValue: AbstractValue<Domain>] = [:]

  /// The state of memory.
  internal var memory: [AbstractPlace: AbstractObject<Domain>] = [:]

  /// Creates an empty context.
  internal init() {}

  /// Forms a context by merging the contents of `batch`.
  internal init<T: Collection<Self>>(merging batch: T) {
    if let (h, t) = batch.headAndTail {
      self = t.reduce(into: h, { (a, b) in a.merge(b) })
    } else {
      self.init()
    }
  }

  /// Merges `other` into `self`.
  internal mutating func merge(_ other: Self) {
    // Merge the locals.
    for (key, lhs) in locals {
      if let rhs = other.locals[key] {
        // Merge both values conservatively.
        locals[key] = lhs && rhs
      } else {
        // Exclude non-dominating definitions.
        locals[key] = nil
      }
    }

    // Merge the state of the objects in memory.
    memory.merge(other.memory, uniquingKeysWith: &&)
  }

  /// Adds a new place in `self` holding an object `v` and assigns that place to assigned to `i`,
  /// which is in `f`.
  ///
  /// - Requires: `i` is not defined in `self` and its result is different from `.nothing`.
  internal mutating func declareStorage(
    assignedTo i: AnyInstructionIdentity, from f: IRFunction, initially v: Domain
  ) {
    let a = AbstractPlace.root(.register(i))
    let t = f.resolved(f.at(i).type)!.type
    assert(memory[a] == nil, "storage already exists")

    memory[a] = .init(type: t, value: .uniform(v))
    locals[.register(i)] = .place(a)
  }

  /// Returns the result calling `action` with a projection of the object at `location`.
  internal mutating func withObject<T>(
    at location: AbstractPlace, computingLayoutWith typer: inout Typer,
    _ action: (inout AbstractObject<Domain>, inout Typer) -> T
  ) -> T {
    switch location {
    case .root:
      return action(&memory[location]!, &typer)
    case .subplace(let root, let path):
      if path.isEmpty {
        return action(&memory[location]!, &typer)
      } else {
        return modify(&memory[.root(root)]!) { (o) in
          o.withSubobject(at: path, computingLayoutWith: &typer, action)
        }
      }
    }
  }

}

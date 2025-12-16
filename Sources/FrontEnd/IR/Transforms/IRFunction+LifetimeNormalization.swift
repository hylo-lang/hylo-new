import Utilities

extension IRFunction {

  internal mutating func normalizeLifetimes(emittingInto m: Module.ID, using typer: inout Typer) {
    var machine = AbstractMachine(interpreting: self, with: Transfer(emittingInto: m))
    var initial = Transfer.Context()
    for (i, t) in termParameters.enumerated() {
      addParameter(t, offset: i, to: &initial)
    }

    machine.fixedPoint(of: &self, startingFrom: initial, using: &typer)
  }

  /// Configures `context` with the initial state of `p`, which is the `i`-th parameter of `self`.
  private mutating func addParameter(
    _ p: IRParameter, offset i: Int, to context: inout Transfer.Context
  ) {
    let t = resolved(p.type)!.type
    let a = AbstractPlace.root(.parameter(i))
    context.locals[.parameter(i)] = .place(a)

    switch p.access {
    case .let, .inout, .sink:
      context.memory[a] = .init(type: t, value: .uniform(.initialized))
    case .set:
      context.memory[a] = .init(type: t, value: .uniform(.uninitialized))
    case .auto:
      fatalError("invalid IR")
    }
  }

}

private struct Transfer: AbstractTransferFunction {

  /// The module containing the instructions intepreted by this function.
  private let module: Module.ID

  /// A typer for querying type relations and resolve names.
  private var typer: Typer! = nil

  /// The context being updated.
  private var context: Context = .init()

  /// The diagnostics gathered by this transfer function during a call to `apply`.
  private var log: DiagnosticSet = .init()

  /// Creates an instance for interpreting the contents of `m`.
  init(emittingInto m: Module.ID) {
    self.module = m
  }

  mutating func apply(
    _ b: IRBlock.ID, from f: inout IRFunction, in c: inout Context,
    using typer: inout Typer
  ) {
    self.typer = consume typer
    swap(&context, &c)

    defer {
      typer = self.typer.sink()
      swap(&context, &c)
    }

    var pc = f.blocks[b].first
    while let i = pc {
      switch f.tag(of: i) {
      case IRAccess.self:
        pc = interpret(f.castUnchecked(i, to: IRAccess.self), from: &f)
      case IRAccess.End.self:
        pc = interpret(f.castUnchecked(i, to: IRAccess.End.self), from: &f)
      case IRAlloca.self:
        pc = interpret(f.castUnchecked(i, to: IRAlloca.self), from: &f)
      case IRApply.self:
        pc = interpret(f.castUnchecked(i, to: IRApply.self), from: &f)
      case IRProject.self:
        pc = interpret(f.castUnchecked(i, to: IRProject.self), from: &f)
      case IRProject.End.self:
        pc = interpret(f.castUnchecked(i, to: IRProject.End.self), from: &f)
      case IRStore.self:
        pc = interpret(f.castUnchecked(i, to: IRStore.self), from: &f)
      case IRSubfield.self:
        pc = interpret(f.castUnchecked(i, to: IRSubfield.self), from: &f)
      default:
        fatalError("invalid IR")
      }
    }
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAccess.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)

    // Access is expected to be reified at this stage.
    switch s.capabilities.uniqueElement! {
    case .let, .inout, .sink:
      // Operand must be a place.
      let a = context.locals[s.source]!.place!
      var o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })

      // All three effects require that the object be fully initialized.
      if !checkInitialized(o.value, at: s.anchor.site) {
        o.value = .uniform(.initialized)
        context.withObject(at: a, computingLayoutWith: &typer, { (x, _) in x = o })
      }

    case .set:
      // A set access requires that the object be fully uninitialized.
      ensureDeinitialized(at: s.source, insertingDeinitializationBefore: i.erased, in: &f)

    case .auto:
      fatalError("invalid IR")
    }

    context.locals[.register(i.erased)] = context.locals[s.source]
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAccess.End.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.start(of: i)
    let k = f.at(s).capabilities.uniqueElement!
    closeProjection(k, openedBy: s.erased, endedBy: i.erased, in: &f)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAlloca.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    context.declareStorage(assignedTo: i.erased, from: f, initially: .uninitialized)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRApply.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    let t = typer.program.types.cast(f.result(of: s.callee)!.type, to: Arrow.self)

    print(t as Any)
    fatalError("invalid IR")
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProject.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let v: Domain = (f.at(i).access == .set) ? .uninitialized : .initialized
    context.declareStorage(assignedTo: i.erased, from: f, initially: v)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProject.End.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.start(of: i)
    let k = f.at(s).access
    closeProjection(k, openedBy: s.erased, endedBy: i.erased, in: &f)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRStore.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    consume(s.value, with: i.erased, in: f)
    initialize(at: s.target, in: f)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRSubfield.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    let a = context.locals[s.base]!.place!.appending(contentsOf: s.path)
    context.locals[.register(i.erased)] = .place(a)
    return f.instruction(after: i.erased)
  }

  /// Returns the pars of `v` iff it is `.mixed`; otherwise, returns `nil`.
  private func subfields(_ v: AbstractObject<Domain>.Value) -> SubfieldsByInitializationState? {
    guard case .mixed(let subfields) = v else {
      return nil
    }

    var paths = SubfieldsByInitializationState()
    var work = [(parts: subfields, path: IndexPath())]

    while let (parts, prefix) = work.popLast() {
      for i in 0 ..< parts.count {
        let path = prefix.appending(i)
        switch parts[i] {
        case .uniform(.initialized):
          paths.initialized.append(path)
        case .uniform(.uninitialized):
          paths.uninitialized.append(path)
        case .uniform(.consumed(let cs)):
          paths.consumed.append((subfield: path, consumers: cs))
        case .mixed(let ps):
          work.append((parts: ps, path: path))
        }
      }
    }

    return paths
  }

  /// Return the initialized parts of `v`.
  private func initializedParts(_ v: AbstractObject<Domain>.Value) -> [IndexPath] {
    switch v {
    case .uniform(.initialized):
      return [[]]
    case .uniform(.uninitialized), .uniform(.consumed):
      return []
    case .mixed:
      return subfields(v)!.initialized
    }
  }

  /// The consumers of the object.
  private func consumers(_ v: AbstractObject<Domain>.Value) -> Domain.Consumers {
    switch v {
    case .uniform(.initialized), .uniform(.uninitialized):
      return []
    case .uniform(.consumed(let cs)):
      return cs
    case .mixed(let ps):
      return .init(combining: ps.map(consumers(_:)))
    }
  }

  /// Returns `true` iff `v` is fully initialized. Otherwise, reports a diagnostic at `site`
  /// and returns false.
  private mutating func checkInitialized(
    _ v: AbstractObject<Domain>.Value, at site: SourceSpan
  ) -> Bool {
    switch v {
    case .uniform(.initialized):
      return true
    case .uniform(.uninitialized):
      log.insert(.useOfUninitializedObject(at: site))
    case .uniform(.consumed):
      log.insert(.useOfConsumedObject(at: site))
    case .mixed:
      log.insert(.useOfPartialObject(at: site))
    }
    return false
  }

  /// Updates the object at `place`, which is a `set` access, to mark it initialized.
  private mutating func initialize(at place: IRValue, in f: IRFunction) {
    assert(f.isAccess(place, .set), "invalid IR")
    let a = context.locals[place]!.place!
    context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      o.value = .uniform(.initialized)
    }
  }

  /// Updates the object at `place`, which is a `sink` access, to mark it consumed by `consumer`.
  private mutating func consume(
    at place: IRValue, with consumer: AnyInstructionIdentity, in f: IRFunction
  ) {
    assert(f.isAccess(place, .set), "invalid IR")

    // Built-in values are implictly copied.
    let t = f.result(of: place)
    if (t?.type).satisfies(typer.program.types.isBuiltin(_:)) {
      return
    }

    let a = context.locals[place]!.place!
    context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      o.value = .uniform(.consumed(by: [consumer]))
    }
  }

  /// Updates `object` to mark it consumed by `consumer`, reporting a diagnostic if `object` cannot
  /// be consumed.
  private mutating func consume(
    _ object: IRValue, with consumer: AnyInstructionIdentity, in f: IRFunction
  ) {
    let t = f.result(of: object)
    assert(!(t.map(\.isAddress) ?? true))

    // Constant values are synthesized on demand and built-in values are implicitly copied.
    if object.isConstant || (t?.type).satisfies(typer.program.types.isBuiltin(_:)) {
      return
    }

    var v = context.locals[object]!.object!
    switch v.value {
    case .uniform(.initialized):
      v.value = .uniform(.consumed(by: [consumer]))
      context.locals[object] = .object(v)
    default:
      log.insert(.illegalMove(at: f.at(consumer).anchor.site))
    }
  }

  /// Inserts IR to deinitialize `parts` of `object` immediately before `i`, which is in `f`.
  ///
  /// Each part is deinitialized using the conformance of its type to `Hylo.Deinitializable`, which
  /// is looked up in the scope to which `i` is anchored. A diagnostic is reported at the location
  /// to which `i` is anchored for each conformance that can't be resolved.
  private mutating func deinitialize(
    _ parts: [IndexPath], of object: IRValue,
    before i: AnyInstructionIdentity, in f: inout IRFunction
  ) {
    typer.program.withEmitter(insertingIn: module) { (emitter) in
      for p in parts {
        emitter.lowering(before: i, in: &f) { (e) in
          let x = e._subfield(object, at: p)
          e._emitDeinitialize(x)
        }
      }
    }
  }

  private mutating func ensureDeinitialized(
    at place: IRValue, insertingDeinitializationBefore i: AnyInstructionIdentity,
    in f: inout IRFunction
  ) {
    let a = context.locals[place]!.place!
    var o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })
    let parts = initializedParts(o.value)
    if !parts.isEmpty {
      deinitialize(parts, of: place, before: i.erased, in: &f)
      o.value = .uniform(.uninitialized)
      context.withObject(at: a, computingLayoutWith: &typer, { (x, _) in x = o })
    }
  }

  private mutating func closeProjection(
    _ access: AccessEffect,
    openedBy start: AnyInstructionIdentity, endedBy end: AnyInstructionIdentity,
    in f: inout IRFunction,
  ) {
    switch access {
    case .let, .set, .inout:
      // The projection must have defined a place.
      let a = context.locals[.register(start)]!.place!
      var o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })

      // The source is expected to be initialized when the access ends.
      if o.value != .uniform(.initialized) {
        let cs = consumers(o.value)
        if cs.isEmpty {
          log.insert(.uninitializedObject(at: f.at(end).anchor.site))
        } else {
          for c in cs { log.insert(.illegalConsumption(access, at: f.at(c).anchor.site)) }
        }

        // Repair the postcondition.
        o.value = .uniform(.initialized)
        context.withObject(at: a, computingLayoutWith: &typer, { (x, _) in x = o })
      }

    case .sink:
      // The source must be deinitialized when the access ends.
      ensureDeinitialized(at: .register(start), insertingDeinitializationBefore: end, in: &f)

    case .auto:
      fatalError("invalid IR")
    }
  }

  /// The initialization state of an object or sub-object.
  ///
  /// Instances form a lattice whose supremum is `.initialized` and infimum is `.consumed(by: s)`
  /// where `s` is the set of all instructions. The meet of two elements denotes the conservative
  /// superposition of two initialization states.
  enum Domain: AbstractDomain {

    /// A set of consumers.
    typealias Consumers = SortedSet<AnyInstructionIdentity>

    /// Object is initialized.
    case initialized

    /// Object is uninitialized.
    case uninitialized

    /// Object was consumed the users in the payload.
    ///
    /// An object can be consumed by multiple users after merging after in which it's been
    /// consumed by different users.
    ///
    /// - Requires: The payload is not empty.
    case consumed(by: Consumers)

    /// Forms a new state by merging `lhs` with `rhs`.
    static func && (lhs: Self, rhs: Self) -> Self {
      switch lhs {
      case .initialized:
        return rhs

      case .uninitialized:
        return rhs == .initialized ? lhs : rhs

      case .consumed(let a):
        if case .consumed(let b) = rhs {
          return .consumed(by: a.union(b))
        } else {
          return .consumed(by: a)
        }
      }
    }

  }

  /// Classification of a record type's subfields into uninitialized, initialized, and consumed sets.
  private struct SubfieldsByInitializationState {

    /// The paths to the initialized parts.
    var initialized: [IndexPath] = []

    /// The paths to the uninitialized parts.
    var uninitialized: [IndexPath] = []

    /// The paths to the consumed parts, along with the users that consumed them.
    var consumed: [(subfield: IndexPath, consumers: Domain.Consumers)] = []

  }

}

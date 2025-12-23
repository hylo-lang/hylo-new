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

  /// The program containing the module being typed.
  internal var program: Program {
    get { typer.program }
    _modify { yield &typer.program }
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
      case IRAssumeState.self:
        pc = interpret(f.castUnchecked(i, to: IRAssumeState.self), from: &f)
      case IRProject.self:
        pc = interpret(f.castUnchecked(i, to: IRProject.self), from: &f)
      case IRProject.End.self:
        pc = interpret(f.castUnchecked(i, to: IRProject.End.self), from: &f)
      case IRProperty.self:
        pc = interpret(f.castUnchecked(i, to: IRProperty.self), from: &f)
      case IRReturn.self:
        pc = interpret(f.castUnchecked(i, to: IRReturn.self), from: &f)
      case IRStore.self:
        pc = interpret(f.castUnchecked(i, to: IRStore.self), from: &f)
      case IRSubfield.self:
        pc = interpret(f.castUnchecked(i, to: IRSubfield.self), from: &f)
      case IRTypeApply.self:
        pc = interpret(f.castUnchecked(i, to: IRTypeApply.self), from: &f)
      case IRWitnessTable.self:
        pc = interpret(f.castUnchecked(i, to: IRWitnessTable.self), from: &f)
      case IRYield.self:
        pc = interpret(f.castUnchecked(i, to: IRYield.self), from: &f)
      case let t:
        fatalError("unexpected instruction \(t)")
      }
    }
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAccess.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let access = f.at(i)

    // Access is expected to be reified at this stage.
    let k = access.capabilities.uniqueElement!
    switch k {
    case .let, .inout, .sink:
      let a = context.locals[access.source]!.place!
      let o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })
      checkInitialized(object: o, at: f.at(i).anchor.site)
      declare(i, from: f, initially: .initialized)

      // A `sink` access consumes its source.
      if k == .sink {
        context.setValue(.uniform(.consumed(by: [i.erased])), at: a, computingLayoutWith: &typer)
      }

    case .set:
      ensureDeinitialized(place: access.source, before: i.erased, in: &f)
      declare(i, from: f, initially: .uninitialized)

    case .auto:
      fatalError("invalid IR")
    }

    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAccess.End.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let start = f.start(of: i)
    let access = f.at(start)

    // Access is expected to be reified at this stage.
    let k = access.capabilities.uniqueElement!
    switch k {
    case .let, .set, .inout:
      checkInitialized(place: .register(start.erased), at: f.at(i).anchor.site)

      // Assume the postcondition moving forward.
      let a = context.locals[access.source]!.place!
      context.setValue(.uniform(.initialized), at: a, computingLayoutWith: &typer)

    case .sink:
      ensureDeinitialized(place: .register(start.erased), before: i.erased, in: &f)

    case .auto:
      fatalError("invalid IR")
    }

    let s = f.at(i).start
    context.memory[context.locals[s]!.place!] = nil
    context.locals[s] = nil
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAlloca.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    declare(i.erased, from: f, initially: .uninitialized)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRApply.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    let t = f.result(of: s.callee)!.type
    let u = program.types.seenAsTermAbstraction(t)!

    passArgument(.set, s.result, insertingDeinitializationBefore: i.erased, in: &f)
    for (p, v) in zip(program.types[u].inputs, s.arguments) {
      passArgument(p.access, v, insertingDeinitializationBefore: i.erased, in: &f)
    }

    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRAssumeState.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    let a = context.locals[s.storage]!.place!
    let v: Domain = s.initialized ? .initialized : .uninitialized
    context.setValue(.uniform(v), at: a, computingLayoutWith: &typer)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProject.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    let t = f.result(of: s.callee)!.type
    let u = program.types.seenAsTermAbstraction(t)!

    for (p, v) in zip(program.types[u].inputs, s.arguments) {
      applyParameterPrecondition(p.access, v, insertingDeinitializationBefore: i.erased, in: &f)
    }

    let v: Domain = (f.at(i).access == .set) ? .uninitialized : .initialized
    declare(i, from: f, initially: v)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProject.End.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let start = f.start(of: i)
    let project = f.at(start)
    let k = project.access

    switch k {
    case .let, .set, .inout:
      checkInitialized(place: .register(start.erased), at: f.at(i).anchor.site)
    case .sink:
      ensureDeinitialized(place: .register(start.erased), before: i.erased, in: &f)
    case .auto:
      fatalError("invalid IR")
    }

    let t = f.result(of: project.callee)!.type
    let u = program.types.seenAsTermAbstraction(t)!
    for (p, v) in zip(program.types[u].inputs, project.arguments) {
      applyParameterPostcondition(p.access, v)
    }

    let s = f.at(i).start
    context.memory[context.locals[s]!.place!] = nil
    context.locals[s] = nil
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRProperty.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    declare(i.erased, from: f, initially: .initialized)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRReturn.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    for (v, o) in context.locals {
      // Deinitialize outstanding owned values.
      if f.owns(v) {
        let parts = initializedParts(context.memory[o.place!]!.value)
        if !parts.isEmpty && !deinitialize(parts, of: v, before: i.erased, in: &f) {
          // Bail out if something isn't deinitializable.
          break
        }
      }

      // Ensure `set` parameters have been initialized.
      else if f.isParameter(v, .set) {
        checkInitialized(place: v, at: f.at(i).anchor.site)
      }
    }

    // No instruction after terminators
    return nil
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRStore.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    consume(object: s.value, with: i.erased, in: f)
    initialize(place: s.target, in: f)
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

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRTypeApply.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    declare(i.erased, from: f, initially: .initialized)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRWitnessTable.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    declare(i.erased, from: f, initially: .initialized)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRYield.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let o = f.output.projection!
    passArgument(
      program.types[o].access, f.at(i).projectee,
      insertingDeinitializationBefore: i.erased, in: &f)
    return f.instruction(after: i.erased)
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

  /// Reports a diagnostic at `site` iff `object` is not fully initialized.
  private mutating func checkInitialized(object: AbstractObject<Domain>, at site: SourceSpan) {
    switch object.value {
    case .uniform(.initialized):
      break
    case .uniform(.uninitialized):
      log.insert(.useOfUninitializedObject(at: site))
    case .uniform(.consumed):
      log.insert(.useOfConsumedObject(at: site))
    case .mixed:
      log.insert(.useOfPartialObject(at: site))
    }
  }

  /// Reports a diagnostic at `site` iff the object at `place` is not fully initialized.
  private mutating func checkInitialized(place: IRValue, at site: SourceSpan) {
    let a = context.locals[place]!.place!
    let o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })
    checkInitialized(object: o, at: site)
  }

  /// Adds a new place in `self` holding an object `v` and assigns that place to assigned to `i`,
  /// which is in `f`.
  ///
  /// - Requires: `i` is not defined in `self` and its result is different from `.nothing`.
  private mutating func declare<T: InstructionIdentity>(
    _ i: T, from f: IRFunction, initially v: Domain
  ) {
    let a = AbstractPlace.root(.register(i.erased))
    let t = f.resolved(f.at(i.erased).type)!.type
    assert(context.memory[a] == nil, "storage already exists")

    context.memory[a] = .init(type: t, value: .uniform(v))
    context.locals[.register(i.erased)] = .place(a)
  }

  /// Updates the object at `place`, which is a `set` access, to mark it initialized.
  private mutating func initialize(place: IRValue, in f: IRFunction) {
    assert(f.isAccess(place, .set), "invalid IR")
    let a = context.locals[place]!.place!
    context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      o.value = .uniform(.initialized)
    }
  }

  /// Updates the object at `place`, which is a `sink` access, to mark it consumed by `consumer`.
  private mutating func consume(
    place: IRValue, with consumer: AnyInstructionIdentity, in f: IRFunction
  ) {
    assert(f.isAccess(place, .set), "invalid IR")

    // Built-in values are implictly copied.
    let t = f.result(of: place)
    if (t?.type).satisfies(program.types.isBuiltin(_:)) {
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
    object: IRValue, with consumer: AnyInstructionIdentity, in f: IRFunction
  ) {
    let t = f.result(of: object)
    assert(!(t.map(\.isAddress) ?? true))

    // Constant values are synthesized on demand and built-in values are implicitly copied.
    if object.isConstant || (t?.type).satisfies(program.types.isBuiltin(_:)) {
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
  ///
  /// The return value is `true` iff all parts could be deinitialized. Otherwise, a diagnostic is
  /// reported and a call to `Builtin.trap` is inserted before `i`.
  @discardableResult
  private mutating func deinitialize(
    _ parts: [IndexPath], of object: IRValue,
    before i: AnyInstructionIdentity, in f: inout IRFunction
  ) -> Bool {
    program.withEmitter(insertingIn: module) { (emitter) in
      for p in parts {
        // Attempt to resolve and apply a witness of `Deinitializable`.
        let success = emitter.lowering(before: i, in: &f) { (e) in
          let x = e._subfield(object, at: p)
          return e._emitDeinitialize(x)
        }

        // Bail out of one element wasn't deinitializable.
        if !success { return false }
      }
      return true
    }
  }

  private mutating func ensureDeinitialized(
    place: IRValue, before i: AnyInstructionIdentity,
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

  private mutating func applyParameterPrecondition(
    _ k: AccessEffect, _ v: IRValue,
    insertingDeinitializationBefore i: AnyInstructionIdentity, in f: inout IRFunction
  ) {
    switch k {
    case .let, .inout, .sink:
      // All three effects require that the object be fully initialized.
      let a = context.locals[v]!.place!
      let o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })
      checkInitialized(object: o, at: f.at(i).anchor.site)

      // A `sink` access consumes its source.
      if k == .sink {
        context.setValue(.uniform(.consumed(by: [i.erased])), at: a, computingLayoutWith: &typer)
      }

    case .set:
      // A set parameter requires that the argument be uninitialized.
      ensureDeinitialized(place: v, before: i.erased, in: &f)

    case .auto:
      fatalError("invalid IR")
    }
  }

  private mutating func applyParameterPostcondition(_ k: AccessEffect, _ v: IRValue) {
    if k == .set {
      // A set parameter initializes memory.
      let a = context.locals[v]!.place!
      context.setValue(.uniform(.initialized), at: a, computingLayoutWith: &typer)
    }
  }

  private mutating func passArgument(
    _ k: AccessEffect, _ v: IRValue,
    insertingDeinitializationBefore i: AnyInstructionIdentity, in f: inout IRFunction
  ) {
    applyParameterPrecondition(k, v, insertingDeinitializationBefore: i, in: &f)
    applyParameterPostcondition(k, v)
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

extension Transfer.Domain: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .initialized:
      return "◼"
    case .uninitialized:
      return "◻"
    case .consumed(let cs):
      return "◻{\(printer.show(cs.map(IRValue.register)))}"
    }
  }

}

import Utilities

extension IRFunction {

  internal mutating func normalizeLifetimes(emittingInto m: Module.ID, using typer: inout Typer) {
    var initial = Transfer.Context()
    for (i, t) in termParameters.enumerated() {
      addParameter(t, offset: i, to: &initial)
    }

    var transfer = Transfer(emittingInto: m)
    transfer.fixedPoint(interpreting: &self, startingFrom: initial, using: &typer)
  }

  /// Configures `context` with the initial state of `p`, which is the `i`-th parameter of `self`.
  private mutating func addParameter(
    _ p: IRParameter, offset i: Int, to context: inout Transfer.Context
  ) {
    let t = resolved(p.type)!.type
    context.locals[.parameter(i)] = .place(.root(.parameter(i)))

    switch p.access {
    case .let, .inout, .sink:
      context.memory[.parameter(i)] = .init(type: t, value: .uniform(.initialized))
    case .set:
      context.memory[.parameter(i)] = .init(type: t, value: .uniform(.uninitialized))
    case .auto:
      fatalError("invalid IR")
    }
  }

}

/// A transfer function for interpreting IR during lifetime normalization.
private struct Transfer: AbstractTransferFunction {

  /// The module containing the instructions intepreted by this function.
  private let module: Module.ID

  /// A typer for querying type relations and resolve names.
  private var typer: Typer! = nil

  /// The context being updated.
  private var context: Context = .init()

  /// Creates an instance for interpreting the contents of `m`.
  fileprivate init(emittingInto m: Module.ID) {
    self.module = m
  }

  /// The program containing the module being typed.
  private var program: Program {
    get { typer.program }
    _modify { yield &typer.program }
  }

  mutating func apply(
    _ b: IRBlock.ID, from f: inout IRFunction, in c: inout Context,
    precededBy predecessors: SortedDictionary<IRBlock.ID, Context>,
    using typer: inout Typer
  ) -> [IRBlock.ID] {
    self.typer = consume typer
    swap(&context, &c)

    defer {
      typer = self.typer.sink()
      swap(&context, &c)
    }

    // Are there unstable states that need fixing?
    var changed: [IRBlock.ID] = []
    for (k, v) in context.locals {
      switch v {
      case .object(let o):
        assert(unstableParts(o.value).isEmpty)

      case .place(let a):
        let o = context.withObject(at: a, computingLayoutWith: &self.typer, { (o, _) in o })
        let parts = unstableParts(o.value)
        if !parts.isEmpty {
          for (p, c) in predecessors {
            inContext(c) { (me) in
              if me.ensureDeinitialized(parts, at: k, before: f.blocks[p].last!, in: &f) {
                changed.append(p)
              }
            }
          }
        }
      }
    }
    if !changed.isEmpty { return changed }

    // Interpret the instructions of the block.
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
      case IRBranch.self:
        pc = interpret(f.castUnchecked(i, to: IRBranch.self), from: &f)
      case IRConditionalBranch.self:
        pc = interpret(f.castUnchecked(i, to: IRConditionalBranch.self), from: &f)
      case IRLoad.self:
        pc = interpret(f.castUnchecked(i, to: IRLoad.self), from: &f)
      case IRMemoryCopy.self:
        pc = interpret(f.castUnchecked(i, to: IRMemoryCopy.self), from: &f)
      case IRMove.self:
        pc = interpret(f.castUnchecked(i, to: IRMove.self), from: &f)
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

    return []
  }

  /// Interprets `i`, which is in `f`.
  ///
  /// If the access is `let` or `inout`, the source must refer to initialized memory and the
  /// instruction defines a new register referring to initialized memory.
  ///
  ///     k ∈ {let, inout}
  ///     ρ = [%x ↦ [%p]] ; μ = [%p ↦ ◼ as T]
  ///     ---
  ///     %i = access [k] %x
  ///     ---
  ///     ρ' = ρ[%i ↦ [%i]] ; μ' = μ[%i ↦ ◼ as T]
  ///
  /// If the access is `sink`, the source must refer to initialized memory and the instruction
  /// defines a new register referring to initialized memory, consuming the source.
  ///
  ///     ρ = [%x ↦ [%p]] ; μ = [%p ↦ ◼ as T]
  ///     ---
  ///     %i = access [sink] %x
  ///     ---
  ///     ρ' = ρ[%i ↦ [%i]] ; μ' = μ[%i ↦ ◼ as T, %p ↦ ◻ as T]
  ///
  /// If the access is `set`, the instruction defines a new register referring to uninitialized
  /// memory. Deinitialization of the parts of the source that are still initialized is inserted
  /// before the instruction if necessary to ensure that the source is fully uninitialized before
  /// the access is formed.
  ///
  ///     ρ = [%x ↦ [%p]] ; μ = [%p ↦ ◻ as T]
  ///     ---
  ///     %i = access [set] %x
  ///     ---
  ///     ρ' = ρ[%i ↦ [%i]] ; μ' = μ[%i ↦ ◻ as T]
  ///
  private mutating func interpret(
    _ i: IRAccess.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let access = f.at(i)

    // Access is expected to be reified at this stage.
    let k = access.capabilities.uniqueElement!
    switch k {
    case .let, .inout, .sink:
      checkInitialized(place: access.source, in: f, at: access.anchor.site)
      declare(i, from: f, initially: .initialized)

      // A `sink` access consumes its source.
      if k == .sink {
        consume(place: access.source, with: i.erased, in: f)
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
    let source = f.at(i).start
    let opener = f.at(f.start(of: i))

    // Access is expected to be reified at this stage.
    let k = opener.capabilities.uniqueElement!
    switch k {
    case .let, .set, .inout:
      checkInitialized(place: f.at(i).start, in: f, at: f.at(i).anchor.site)

      // Assume the postcondition moving forward.
      let a = context.locals[opener.source]!.place!
      context.updateValue(.uniform(.initialized), at: a, computingLayoutWith: &typer)

    case .sink:
      ensureDeinitialized(place: f.at(i).start, before: i.erased, in: &f)

    case .auto:
      fatalError("invalid IR")
    }

    context.memory[source] = nil
    context.locals[source] = nil
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
    context.updateValue(.uniform(v), at: a, computingLayoutWith: &typer)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRBranch.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRConditionalBranch.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    assert(context.locals[f.at(i).condition]!.object!.value == .uniform(.initialized))
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRLoad.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    consume(place: s.source, with: i.erased, in: f)
    declare(i, from: f, initially: .initialized)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRMemoryCopy.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    let s = f.at(i)
    consume(place: s.source, with: i.erased, in: f)
    initialize(place: s.target, in: f)
    return f.instruction(after: i.erased)
  }

  /// Interprets `i`, which is in `f`.
  private mutating func interpret(
    _ i: IRMove.ID, from f: inout IRFunction
  ) -> AnyInstructionIdentity? {
    // Determine the semantics of the move.
    let s = f.at(i)
    let k: AccessEffect = isInitialized(place: s.target) ? .inout : .set

    // Emit the move.
    program.withEmitter(insertingIn: module) { (emitter) in
      emitter.lowering(after: i.erased, in: &f) { (e) in
        e._emitMove([k], s.source, to: s.target)
      }
    }

    // Removes the `move` instruction and sets the PC right after.
    return f.remove(i.erased)
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
    let source = f.at(i).start
    let opener = f.at(f.start(of: i))

    switch opener.access {
    case .let, .set, .inout:
      checkInitialized(place: source, in: f, at: f.at(i).anchor.site)
    case .sink:
      ensureDeinitialized(place: source, before: i.erased, in: &f)
    case .auto:
      fatalError("invalid IR")
    }

    let t = f.result(of: opener.callee)!.type
    let u = program.types.seenAsTermAbstraction(t)!
    for (p, v) in zip(program.types[u].inputs, opener.arguments) {
      applyParameterPostcondition(p.access, v)
    }

    context.memory[source] = nil
    context.locals[source] = nil
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
      if f.owns(v), case .place(.root(let root)) = o {
        let parts = initializedParts(context.memory[root]!.value)
        if !parts.isEmpty && !deinitialize(parts, at: v, before: i.erased, in: &f) {
          // Bail out if something isn't deinitializable.
          break
        }
      }

      // Ensure `set` parameters have been initialized.
      else if f.isParameter(v, .set) {
        checkInitialized(place: v, in: f, at: f.at(i).anchor.site, beforeReturning: true)
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
        case .uniform(.consumed(let us)):
          paths.consumed.append((subfield: path, consumers: us))
        case .uniform(.phi):
          paths.unstable.append(path)
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
    case .uniform(let w):
      return (w == .initialized) ? [[]] : []
    case .mixed:
      return subfields(v)!.initialized
    }
  }

  /// Return the parts of `v` whose initialization state depends on control-flow.
  private func unstableParts(_ v: AbstractObject<Domain>.Value) -> [IndexPath] {
    switch v {
    case .uniform(let w):
      return (w == .phi) ? [[]] : []
    case .mixed:
      return subfields(v)!.unstable
    }
  }

  /// The consumers of the object.
  private func consumers(_ v: AbstractObject<Domain>.Value) -> Domain.Users {
    switch v {
    case .uniform(.initialized), .uniform(.uninitialized), .uniform(.phi):
      return []
    case .uniform(.consumed(let us)):
      return us
    case .mixed(let ps):
      return .init(combining: ps.map(consumers(_:)))
    }
  }

  /// Returns `true` iff the object stored at `place` is fully initialized.
  private mutating func isInitialized(place: IRValue) -> Bool {
    let a = context.locals[place]!.place!
    return context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      o.value == .uniform(.initialized)
    }
  }

  /// Reports a diagnostic at `site` iff the object stored at `place`, which is in `f`, is not
  /// fully initialized.
  ///
  /// A specialized diagnostic is reported if `isBeforeReturning` is `true` and `place` denotes the
  /// storage of a `set` parameter that is (partially) moved or uninitialized object.
  private mutating func checkInitialized(
    place: IRValue, in f: IRFunction, at site: SourceSpan,
    beforeReturning isBeforeReturning: Bool = false
  ) {
    let a = context.locals[place]!.place!
    let o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })

    switch o.value {
    case .uniform(.initialized):
      // All is well if the object is indeed initialized.
      break

    case _ where isBeforeReturning && (place.parameter != nil):
      // Report a failure to initialize a `set` parameter before returning.
      if place == f.returnRegister {
        report(.init(.error, "missing return value", at: site))
      } else {
        report(.init(.error, "'set' parameter not initialized before exit", at: site))
      }

    case .uniform(.uninitialized), .uniform(.phi):
      report(.useOfUninitializedObject(at: site))
    case .uniform(.consumed):
      report(.useOfConsumedObject(at: site))
    case .mixed:
      report(.useOfPartialObject(at: site))
    }
  }

  /// Updates the context to define register `i`, which is in `f`.
  ///
  /// `i` identifies a register in `f` that results in either an object or a place. In the first
  /// case, an new object is assigned to `i` directly. In the second case, a new place is created
  /// to contain the new oject and the register is assigned to that place.
  ///
  /// The new object is defined as a uniform value `v`.
  private mutating func declare<T: InstructionIdentity>(
    _ i: T, from f: IRFunction, initially v: Domain
  ) {
    assert(context.locals[.register(i.erased)] == nil, "register is already assigned")

    // Create a new object.
    let t = f.resolved(f.at(i.erased).type)!
    let o = AbstractObject(type: t.type, value: .uniform(v))

    // If the register defines an address, create a new place and assigns it the new object.
    if t.isAddress {
      assert(context.memory[.register(i.erased)] == nil, "storage already exists")
      context.memory[.register(i.erased)] = .init(type: t.type, value: .uniform(v))
      context.locals[.register(i.erased)] = .place(.root(.register(i.erased)))
    }

    // Otherwise, assigns the new object to the register itself.
    else {
      context.locals[.register(i.erased)] = .object(o)
    }
  }

  /// Updates the object stored at `place`, which is a `set` access, to mark it initialized.
  private mutating func initialize(place: IRValue, in f: IRFunction) {
    assert(f.isAccess(place, .set), "invalid IR")
    let a = context.locals[place]!.place!
    context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      o.value = .uniform(.initialized)
    }
  }

  /// Updates the object stored at `place` to mark it consumed by `consumer`.
  private mutating func consume(
    place: IRValue, with consumer: AnyInstructionIdentity, in f: IRFunction
  ) {
    let t = f.result(of: place)!
    assert(t.isAddress)

    // Built-in values are implictly copied.
    if program.types.isBuiltin(t.type) {
      return
    }

    let a = context.locals[place]!.place!
    var d: Diagnostic? = nil
    context.withObject(at: a, computingLayoutWith: &typer) { (o, _) in
      switch o.value {
      case .uniform(.initialized):
        o.value = .uniform(.consumed( [consumer]))
      default:
        d = .some(.illegalMove(at: f.at(consumer).anchor.site))
      }
    }
    d.map({ (d) in report(d) })
  }

  /// Updates `object` to mark it consumed by `consumer`, reporting a diagnostic if `object` cannot
  /// be consumed.
  private mutating func consume(
    object: IRValue, with consumer: AnyInstructionIdentity, in f: IRFunction
  ) {
    let t = f.result(of: object)!
    assert(!t.isAddress)

    // Constant values are synthesized on demand and built-in values are implicitly copied.
    if object.isConstant || program.types.isBuiltin(t.type) {
      return
    }

    var d: Diagnostic? = nil
    modify(&context.locals[object]!) { (local) in
      var o = local.object!
      switch o.value {
      case .uniform(.initialized):
        o.value = .uniform(.consumed([consumer]))
      default:
        d = .some(.illegalMove(at: f.at(consumer).anchor.site))
      }
      local = .object(o)
    }
    d.map({ (d) in report(d) })
  }

  /// Inserts IR to deinitialize the specified `parts` of the object stored at `place` immediately
  /// before `i`, which is in `f`.
  ///
  /// Each part is deinitialized using the conformance of its type to `Hylo.Deinitializable`, which
  /// is looked up in the scope to which `i` is anchored. A diagnostic is reported at the location
  /// to which `i` is anchored for each conformance that can't be resolved.
  ///
  /// The return value is `true` iff all parts could be deinitialized. Otherwise, a diagnostic is
  /// reported and a call to `Builtin.trap` is inserted before `i`.
  @discardableResult
  private mutating func deinitialize(
    _ parts: [IndexPath], at place: IRValue,
    before i: AnyInstructionIdentity, in f: inout IRFunction
  ) -> Bool {
    // Nothing to do if `parts` is empty.
    if parts.isEmpty { return true }

    // Otherwise, construct an emitter to insert deinitialization.
    return program.withEmitter(insertingIn: module) { (emitter) in
      for p in parts {
        // Attempt to resolve and apply a witness of `Deinitializable`.
        let success = emitter.lowering(before: i, in: &f) { (e) in
          let x = e._subfield(place, at: p)
          return e._emitDeinitialize(x)
        }

        // Bail out of one element wasn't deinitializable.
        if !success { return false }
      }
      return true
    }
  }

  /// Ensures that the objects identified by `parts` relative to `place` are deinitialized,
  /// inserting deinitialization before `i`, which is in `f`, is necessary.
  private mutating func ensureDeinitialized(
    _ parts: [IndexPath], at place: IRValue,
    before i: AnyInstructionIdentity, in f: inout IRFunction
  ) -> Bool {
    let a = context.locals[place]!.place!
    let o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })
    let initialized = parts.filter(initializedParts(o.value).contains(_:))
    if !initialized.isEmpty {
      return deinitialize(initialized, at: place, before: i, in: &f)
    } else {
      return false
    }
  }

  /// Ensures that the object stored at `place`, if any, is fully deinitialized, inserting
  /// deinitialization before `i`, which is in `f`, is necessary.
  private mutating func ensureDeinitialized(
    place: IRValue, before i: AnyInstructionIdentity,
    in f: inout IRFunction
  ) {
    let a = context.locals[place]!.place!
    var o = context.withObject(at: a, computingLayoutWith: &typer, { (o, _) in o })
    let initialized = initializedParts(o.value)
    if !initialized.isEmpty {
      deinitialize(initialized, at: place, before: i.erased, in: &f)
      o.value = .uniform(.uninitialized)
      context.withObject(at: a, computingLayoutWith: &typer, { (x, _) in x = o })
    }
  }

  /// Ensures that the state of the object stored at place `v` statisfies the preconditions of a
  /// parameter `k`, inserting deinitialization before `i`, which is in `f`, is necessary.
  private mutating func applyParameterPrecondition(
    _ k: AccessEffect, _ v: IRValue,
    insertingDeinitializationBefore i: AnyInstructionIdentity, in f: inout IRFunction
  ) {
    switch k {
    case .let, .inout, .sink:
      // All three effects require that the object be fully initialized.
      let a = context.locals[v]!.place!
      checkInitialized(place: v, in: f, at: f.at(i).anchor.site)

      // A `sink` access consumes its source.
      if k == .sink {
        context.updateValue(.uniform(.consumed([i.erased])), at: a, computingLayoutWith: &typer)
      }

    case .set:
      // A set parameter requires that the argument be uninitialized.
      ensureDeinitialized(place: v, before: i.erased, in: &f)

    case .auto:
      fatalError("invalid IR")
    }
  }

  /// Ensures that the state of the object stored at place `v` statisfies the postconditions of a
  /// parameter `k`.
  private mutating func applyParameterPostcondition(_ k: AccessEffect, _ v: IRValue) {
    if k == .set {
      // A set parameter initializes memory.
      let a = context.locals[v]!.place!
      context.updateValue(.uniform(.initialized), at: a, computingLayoutWith: &typer)
    }
  }

  /// Ensures that the state of the object stored at place `v` statisfies the pre/postconditions of
  /// a parameter `k`, inserting deinitialization before `i`, which is in `f`, is necessary.
  private mutating func passArgument(
    _ k: AccessEffect, _ v: IRValue,
    insertingDeinitializationBefore i: AnyInstructionIdentity, in f: inout IRFunction
  ) {
    applyParameterPrecondition(k, v, insertingDeinitializationBefore: i, in: &f)
    applyParameterPostcondition(k, v)
  }

  /// Returns the result of calling `action` on `self` configured with context `c`.
  private mutating func inContext<T>(_ c: Context, _ action: (inout Self) -> T) -> T {
    var current = context
    context = c
    defer { swap(&context, &current) }
    return action(&self)
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// The initialization state of an object or sub-object.
  ///
  /// Instances form a lattice whose supremum is `.initialized` and infimum is `.consumed(by: s)`
  /// where `s` is the set of all instructions. The meet of two elements denotes the conservative
  /// superposition of two initialization states.
  enum Domain: AbstractDomain {

    /// A set of instructions having consumed or borrowed a value.
    typealias Users = SortedSet<AnyInstructionIdentity>

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
    case consumed(Users)

    /// Object's state depends on the previous basic block having been executed.
    ///
    /// An object has a "phi" state in a basic block C iff it is simultaneously initialized at the
    /// exit of a block A and uninitialized/consumed at the exist of another block B, and both A
    /// B are predeceddors of C.
    ///
    /// The term "phi" refers to the notion of a phi node in SSA, which denotes a related concept.
    case phi

    /// Forms a new state by merging `lhs` with `rhs`.
    static func && (lhs: Self, rhs: Self) -> Self {
      switch (lhs, rhs) {
      case (let x, let y) where x == y:
        return x
      case (.uninitialized, .consumed):
        return rhs
      case (.consumed, .uninitialized):
        return lhs
      case (.consumed(let a), .consumed(let b)):
        return .consumed(a.union(b))
      default:
        return .phi
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
    var consumed: [(subfield: IndexPath, consumers: Domain.Users)] = []

    /// The paths to parts whose values depend on control-flow.
    var unstable: [IndexPath] = []

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
    case .consumed(let us):
      return "◻{\(printer.show(us.map(IRValue.register)))}"
    case .phi:
      return "φ"
    }
  }

}

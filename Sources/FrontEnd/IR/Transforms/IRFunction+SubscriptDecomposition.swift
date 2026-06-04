import DequeModule
import OrderedCollections

extension IRFunction {

  internal mutating func decompose(emittingInto m: Module.ID, using typer: inout Typer) {
    // Nothing to do if the function isn't a subscript or isn't defined.
    if !isSubscript || !isDefined { return }

    /// The control-flow graph of the subscript.
    let cfg = controlFlow()
    /// The dominance relation of the subscript.
    let dominance = DominatorTree(function: self, controlFlow: cfg).children()
    /// The blocks in the ramp.
    var rampBlocks: [IRBlock.ID] = .init()
    /// The parameters and allocations of the ramp that may be accessed from the slide.
    var frameValues: [IRValue] = termParameters.indices.map(IRValue.parameter(_:))
    /// The `yield` instructions at the root of the slides.
    var slideRoots: [AnyInstructionIdentity] = .init()

    // Partition the function into ramp and slides, making sure iterating over the ramp list
    // guarantees that definitions are visited before their uses.
    var work = [entry!]
    while let b = work.popLast() {
      rampBlocks.append(b)

      var endOfRamp: AnyInstructionIdentity? = nil
      for i in instructions(in: b) {
        switch tag(of: i) {
        case IRAlloca.self:
          frameValues.append(.register(i))
        case IRYield.self:
          endOfRamp = i
        default:
          continue
        }

        // There's no need to continue if we found a `yield` instruction.
        if endOfRamp != nil { break }
      }

      if let y = endOfRamp {
        slideRoots.append(y)
      } else {
        work.append(contentsOf: dominance[b] ?? [])
      }
    }

    typer.program.withEmitter(insertingIn: m) { (emitter) in
      emitter.defineRamp(self, covering: rampBlocks, transferring: frameValues)
      for y in slideRoots {
        emitter.defineSlide(self, root: y, receiving: frameValues, cfg: cfg)
      }
    }
  }

  internal mutating func replaceSubscriptApplications() {
  }

}

extension IREmitter {

  /// Returns the identity of the existentialized form of the polymorphic function `f`.
  fileprivate mutating func demandRamp(_ source: IRFunction) -> IRFunction.ID {
    assert(source.isSubscript && source.isDefined)

    // Has the ramp been demanded already?
    let n = IRFunction.Name.ramp(source.name)
    if let i = program[module].ir.functions.index(forKey: n) {
      return i
    }

    // The ramp takes one extra parameter denoting the plateau using the projection and one
    // denoting the return register. Type parameters are left unchanged.
    var ps: [IRParameter] = .init(minimumCapacity: source.termParameters.count + 2)
    ps.append(contentsOf: source.termParameters)

    let ptr = program.types.demand(MachineType.ptr)
    // let slide = program.types.demand(
    //   FunctionPointer(inputs: [pointer.erased, pointer.erased], output: .void))

    let p = Parameter(access: .let, type: ptr.erased)
    // let q = Parameter(access: .let, type: slide.erased)
    let plateau = program.types.demand(Arrow(inputs: [p, p/*, q */], output: .void))

    ps.append(.init(type: plateau.erased, access: .let, declaration: nil))
    ps.append(.init(type: .void, access: .set, declaration: nil))

    let ramp = IRFunction(
      name: n, output: .indirect, typeParameters: source.typeParameters,
      termParameters: ps)
    return program[module].ir.addFunction(ramp)
  }

  // Create the ramp and copy its contents, assuming there is no `project` in the source.
  fileprivate mutating func defineRamp(
    _ source: IRFunction, covering rampBlocks: [IRBlock.ID], transferring frameValues: [IRValue],
  ) {
    let f = demandRamp(source)
    var ramp = program[module].ir[f].move()
    defer { program[module].ir[f].take(definition: ramp) }

    let ptr = program.types.demand(MachineType.ptr)
    let frameType = program.types.buffer(ptr.erased, count: frameValues.count)

    // The plateau is the penultimate parameter of the ramp.
    let plateau = IRValue.parameter(ramp.termParameters.count - 2)

    var table = IRSubstitutionTable()
    for b in rampBlocks { table[b] = ramp.addBlock() }

    // Allocate and start initializing the frame that will be piped through the slide.
    let head = source.at(source.instructions(in: source.entry!).head!).anchor
    let frame = lowering(.end(of: table[source.entry!]), anchoredTo: head, in: &ramp) { (e) in
      let x0 = e._alloca(frameType)
      for i in source.termParameters.indices {
        let x1 = e._subfield(x0, at: [i])
        let x2 = e._apply_builtin(.addressOf, to: [.parameter(i)])
        e._emitInitialize(x1, with: x2)
      }

      return x0
    }

    for b in rampBlocks {
      for i in source.instructions(in: b) {
        let s = source.at(i)

        if let y = s as? IRYield {
          lowering(.end(of: table[b]), anchoredTo: y.anchor, in: &ramp) { (e) in
            // `x0` stores a pointer to the value being projected.
            let x0 = e._alloca(ptr.erased)
            // `x2` stores the return value of the plateau (which is a unit).
            let x2 = e._alloca(.void)

            // Store the address to the projected value to an alloca.
            let x3 = e._apply_builtin(.addressOf, to: [table[y.projectee]])
            e._emitInitialize(x0, with: x3)

            // Apply the plateau and return.
            _ = e._apply(plateau, [x0, frame], into: x2, afterFormingAccesses: true)
            e._return()
          }
          break
        }

        else {
          lowering(.end(of: table[b]), anchoredTo: s.anchor, in: &ramp) { (e) in
            let x0 = e._clone(i, from: source, substitutingOperandsWith: &table)
            if let j = frameValues.firstIndex(of: IRValue.register(i)) {
              let x1 = e._subfield(frame, at: [j])
              let x2 = e._apply_builtin(.addressOf, to: [x0!])
              e._emitInitialize(x1, with: x2)
            }
          }
        }
      }
    }

    print(program.show(ramp))
  }

  fileprivate mutating func demandSlide(
    _ source: IRFunction, root: AnyInstructionIdentity
  ) -> IRFunction.ID {
    assert(source.isSubscript && source.isDefined)

    // Has the ramp been demanded already?
    let n = IRFunction.Name.slide(source.name, source.block(defining: root).rawValue)
    if let i = program[module].ir.functions.index(forKey: n) {
      return i
    }

    let ptr = program.types.demand(MachineType.ptr)
    let p = IRParameter(type: ptr.erased, access: .let, declaration: nil)
    let q = IRParameter(type: .void, access: .set, declaration: nil)

    let slide = IRFunction(
      name: n, output: .indirect, typeParameters: source.typeParameters,
      termParameters: [p, p, q])
    return program[module].ir.addFunction(slide)
  }

  fileprivate mutating func defineSlide(
    _ source: IRFunction, root: AnyInstructionIdentity, receiving frameValues: [IRValue],
    cfg: ControlFlowGraph
  ) {
    let f = demandSlide(source, root: root)
    var slide = program[module].ir[f].move()
    defer { program[module].ir[f].take(definition: slide) }

    let ptr = program.types.demand(MachineType.ptr)
    let frameType = program.types.buffer(ptr.erased, count: frameValues.count)

    let entry = source.block(defining: root)
    var table = IRSubstitutionTable()
    for b in cfg.reachable(from: entry) { table[b] = slide.addBlock() }

    let head = source.at(root).anchor
    lowering(.end(of: table[entry]), anchoredTo: head, in: &slide) { (e) in
      let frame = e._pointer_cast(.parameter(1), as: frameType.erased)
      for (i, v) in frameValues.enumerated() {
        table[v] = e._subfield(frame, at: [i])
      }
    }

    for i in source.instructions(after: root) {
      let s = source.at(i)
      lowering(.end(of: table[entry]), anchoredTo: s.anchor, in: &slide) { (e) in
        _ = e._clone(i, from: source, substitutingOperandsWith: &table)
      }
    }
  }

}

import Utilities

extension IREmitter {

  /// Replaces calls to polymorphic functions in `f` with calls to monomorphic functions, using the
  /// given type witness arguments during existentialization.
  ///
  /// - Parameters:
  ///   - f: The function to depolymorphize.
  ///   - witnesses: A map a type to its to the corresponding term parameter representing its
  ///     witness at compile-time. This table is empty unless the method is called to finalize
  ///     the existentialization of `f` (see `existentialize(_:into:)`).
  internal mutating func depolymorphize(
    _ f: inout IRFunction, passing witnesses: consuming [AnyTypeIdentity: IRValue] = [:]
  ) {
    var work = Array(f.instructions())
    while let i = work.popLast() {
      switch f.tag(of: i) {
      case IRTypeApply.self:
        depolymorphize(f.castUnchecked(i, to: IRTypeApply.self), in: &f, reusing: &witnesses)
      default:
        continue
      }
    }

    // Close the `let` accesses that may have been opened to pass type witnesses.
    f.closeOpenEndedRegions()
  }
  
  /// Replaces uses of `i` with their existentialized forms.
  private mutating func depolymorphize(
    _ i: IRTypeApply.ID, in f: inout IRFunction,
    reusing witnesses: inout [AnyTypeIdentity: IRValue]
  ) {
    // Remove the instruction if it has no use.
    if f.uses[.register(i.erased), default: []].isEmpty {
      f.remove(i.erased)
      return
    }

    // Otherwise, replace the type application's arguments with type witnesses. The way in which
    // this substitution is done depends on the way the type application is used.
    switch f.at(i).callee {
    case .function(let c, _):
      depolymorphize(c, operandOf: i, in: &f, reusing: &witnesses)

    default:
      unimplemented("first class function deploymorphization")
    }
  }
  
  /// Replaces uses of `i`, which is a type application of the polymorphic function `c`, with their
  /// existentialized forms.
  private mutating func depolymorphize(
    _ c: IRFunction.Name, operandOf i: IRTypeApply.ID, in f: inout IRFunction,
    reusing witnesses: inout [AnyTypeIdentity: IRValue]
  ) {
    let application = f.at(i)

    // Demand the declaration of the existentialized version of the callee. Note that the
    // definition of this function may not live in the same module as `f`.
    let poly = program[module].ir.functions[c]!
    let mono = demandExistentialized(poly)

    // Get the types of the parameters of the original poloymorphic function.
    let parameters = poly.termParameters.map({ (p) in f.resolved(p.type)!.type })

    // Create an array with a type witness for each of the type argument passed to `i`. These
    // witnesses will be concatenated with the term arguments of each use application of `c`
    // instantiated by `i`.
    let witnesses = lowering(before: i.erased, in: &f) { (e) in
      application.arguments.values.map { (a) in
        e._emitTypeWitness(of: a.erased, reusing: &witnesses)
      }
    }

    // Update the uses of the type application.
    for u in f.uses[.register(i.erased)]! {
      switch f.tag(of: u.user) {
      case IRApply.self where u.index == 0:
        // `i` is used as a callee in an ordinary function application.
        depolymorphize(
          polymorphicApplyUser: u.user, with: mono,
          passing: witnesses, to: parameters, in: &f)

      case IRProject.self where u.index == 0:
        depolymorphize(
          polymorphicProjectUser: u.user, with: mono,
          passing: witnesses, to: parameters, in: &f)

      default:
        unimplemented()
      }
    }

    // Remove the type application, now that all its uses have been replaced.
    f.remove(i.erased)
  }

  /// Replaces `u`, which is the application of a polymorphic abstraction, with an application of
  /// `mono`, which is the existentialized form of `u`'s callee.
  ///
  /// - Parameters:
  ///   - user: The user of a `type_apply` instantiating the polymorphic function of which `mono`is
  ///     the existentialization.
  ///   - mono: The identity of an existentialized function.
  ///   - witnesses: witnesses for each type paramete in the original polymorphic function.
  ///   - parameters: The types of the term parameters of the polymorphic function.
  ///   - f: The function containing`uer`.
  private mutating func depolymorphize(
    polymorphicApplyUser user: AnyInstructionIdentity, with mono: IRFunction.ID,
    passing witnesses: [IRValue], to parameters: [AnyTypeIdentity], in f: inout IRFunction
  ) {
    let old = f.at(user) as! IRApply

    var xs = witnesses
    let result = lowering(before: user, in: &f) { (e) in
      for (a, p) in zip(old.arguments, parameters) { xs.append(e._emitCast(a, to: p)) }
      return e._emitCast(old.result, to: parameters.last!)
    }

    let referenceToMono = functionReference(referringTo: mono)
    let s = IRApply(callee: referenceToMono, arguments: xs, result: result, anchor: old.anchor)
    f.replace(user, with: s)
  }

  /// Replaces `u`, which is the application of a polymorphic abstraction, with an application of
  /// `mono`, which is the existentialized form of `u`'s callee.
  ///
  /// This method is similar to `depolymorphize(polymorphicApplyUser:with:passing:to:in:)` only for
  /// the case where `user` is a projection rather thanan application.
  private mutating func depolymorphize(
    polymorphicProjectUser user: AnyInstructionIdentity, with mono: IRFunction.ID,
    passing witnesses: [IRValue], to parameters: [AnyTypeIdentity], in f: inout IRFunction
  ) {
    let old = f.at(user) as! IRProject

    var xs = witnesses
    lowering(before: user, in: &f) { (e) in
      for (a, p) in zip(old.arguments, parameters) { xs.append(e._emitCast(a, to: p)) }
    }

    let referenceToMono = functionReference(referringTo: mono)
    let s = IRProject(
      callee: referenceToMono, arguments: xs, projectee: old.projectee, access: old.access,
      anchor: old.anchor)

    // Cast the result of the projection if necessary.
    let t = f.result(of: .register(user))!.type
    if !t[.hasGenericParameter] {
      assert(t == f.resolved(s.type)!.type)
      f.replace(user, with: s)
    } else {
      let x0 = insert(s)
      f.replace(user, with: IRPlaceCast(source: x0!, target: t, anchor: old.anchor))
    }
  }

  /// Returns the identity of the existentialized form of the polymorphic function `f`.
  private mutating func demandExistentialized(_ poly: IRFunction) -> IRFunction.ID {
    assert(!poly.isMonomorphic)

    // Has the function been existentialized already?
    let n = IRFunction.Name.existentialized(poly.name)
    if let i = program[module].ir.functions.index(forKey: n) {
      return i
    }

    // The existentialized form of the function takes the generic parameter as type witnesses
    // before the term parameters of the polymorphic form.
    var ps: [IRParameter] = .init(
      minimumCapacity: poly.typeParameters.count + poly.termParameters.count)
    for p in poly.typeParameters {
      let t = program.types.demand(TypeWitness()).erased
      let u = IRType.lowered(t, isAddress: true)
      let d = program.types[p].declaration.map(DeclarationIdentity.init(_:))
      ps.append(.init(type: u, access: .let, declaration: d))
    }

    ps.append(contentsOf: poly.termParameters)
    let mono = IRFunction(name: n, output: poly.output, typeParameters: [], termParameters: ps)
    return program[module].ir.addFunction(mono)
  }

  /// Emits the existentialized definition of `f` into `g`.
  internal mutating func existentialize(_ f: IRFunction.ID, into g: IRFunction.ID) {
    let poly = program[module].ir[f]
    var mono = program[module].ir[g].move()
    assert(poly.isDefined && !mono.isDefined, "existentialization already completed")

    /// The type parameters of the function being existentialized.
    let parameters = poly.typeParameters

    /// A table mapping type parameters from the source to their corresponding term parameters in
    /// the existentialized translation.
    var witnesses: [AnyTypeIdentity: IRValue] = .init(
      uniqueKeysWithValues: parameters.enumerated().map({ (i, p) in (p.erased, .parameter(i)) }))

    /// A table for rewriting instructions.
    var properties = IRSubstitutionTable()
    for b in poly.blocks.addresses {
      properties[b] = mono.addBlock()
    }
    for i in poly.termParameters.indices {
      properties[IRValue.parameter(i)] = .parameter(i + parameters.count)
    }

    // Iterate over the basic blocks in such a way that definitions are visited before their uses.
    let cfg = poly.controlFlow()
    let dominance = DominatorTree(function: poly, controlFlow: cfg)
    for b in dominance.bfs {
      for i in poly.instructions(in: b) {
        /// Where the next instruction should be inserted.
        let p = InsertionPoint.end(of: properties[b])

        switch poly.tag(of: i) {
        case IRAlloca.self:
          let s = poly.at(i) as! IRAlloca
          lowering(p, anchoredTo: s.anchor, in: &mono) { (me) in
            // Gather the generic type parameters that occur free in type of the storage being
            // allocated. They should be defined by the function being existentialized.
            let ps = me.program.types.parameters(freeIn: s.storage)
            assert(ps.allSatisfy(parameters.contains(_:)))

            // If there isn't any generic parameter, we can simply copy the `alloca`. Otherwise,
            // we have to replace it with an `allocx` applied to a run-time type witness.
            if ps.isEmpty {
              properties[.register(i)] = me.insert(s)!
            } else {
              let w = me._emitTypeWitness(of: s.storage, reusing: &witnesses)
              properties[.register(i)] = me._allocx(w, as: s.storage, alignment: s.alignment)
            }
          }

        default:
          let s = poly.at(i)
          lowering(p, anchoredTo: s.anchor, in: &mono) { (me) in
            if let clone = me.insert(s.substituting(properties)) {
              properties[.register(i)] = clone
            }
          }
        }
      }
    }

    depolymorphize(&mono, passing: witnesses.filter({ (k, v) in v.parameter != nil }))
    program[module].ir[g].take(definition: mono)
  }

}

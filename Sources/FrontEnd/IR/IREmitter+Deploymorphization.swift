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
    let ws: SortedSet<AnyInstructionIdentity> = witnesses.values.reduce(into: []) { (r, w) in
      if let us = f.uses[w] { r.formUnion(us.map(\.user)) }
    }
    f.closeOpenEndedRegions(in: ws)
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
      let k = program[module].ir.identity(function: c)!
      depolymorphize(k, operandOf: i, in: &f, reusing: &witnesses)

    default:
      unimplemented("first class function deploymorphization")
    }
  }
  
  /// Replaces uses of `i`, which is a type application of the polymorphic function `c`, with their
  /// existentialized forms.
  private mutating func depolymorphize(
    _ c: IRFunction.ID, operandOf i: IRTypeApply.ID, in f: inout IRFunction,
    reusing witnesses: inout [AnyTypeIdentity: IRValue]
  ) {
    let application = f.at(i)

    // Demand the declaration of the existentialized version of the callee. Note that the
    // definition of this function may not live in the same module as `f`.
    let poly = program[module].ir[c]
    let mono = demandExistentialized(poly)

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
          passing: witnesses, to: poly.termParameters, in: &f)

      case IRProject.self where u.index == 0:
        depolymorphize(
          polymorphicProjectUser: u.user, with: mono,
          passing: witnesses, to: poly.termParameters, in: &f)

      default:
        unimplemented()
      }
    }

    // Remove the type application, now that all its uses have been replaced.
    f.remove(i.erased)
  }

  /// Replaces `user`, which is the application of a polymorphic abstraction, with an application
  /// of `mono`, which is the existentialized form of `u`'s callee.
  ///
  /// - Parameters:
  ///   - user: An `apply` instruction whose callee is the result of a `type_apply` instantiating
  ///     the polymorphic function, of which `mono`is the existentialization.
  ///   - mono: The identity of an existentialized function.
  ///   - witnesses: witnesses for each type parameter in the original polymorphic function.
  ///   - parameters: The types of the term parameters of the polymorphic function.
  ///   - f: The function containing `user`.
  private mutating func depolymorphize(
    polymorphicApplyUser user: AnyInstructionIdentity, with mono: IRFunction.ID,
    passing witnesses: [IRValue], to parameters: [IRParameter], in f: inout IRFunction
  ) {
    let old = f.at(user) as! IRApply

    var xs = witnesses
    let result = lowering(before: user, in: &f) { (e) in
      for (a, p) in zip(old.arguments, parameters) {
        xs.append(e._emitCast(a, to: p.access, p.type))
      }
      let last = parameters.last!
      return e._emitCast(old.result, to: last.access, last.type)
    }

    let referenceToMono = functionReference(to: mono)
    f.replace(
      user,
      with: IRApply(callee: referenceToMono, arguments: xs, result: result, anchor: old.anchor))
  }

  /// Replaces `user`, which is the application of a polymorphic abstraction, with an application
  /// of `mono`, which is the existentialized form of `u`'s callee.
  ///
  /// This method is similar to `depolymorphize(polymorphicApplyUser:with:passing:to:in:)`, except
  /// that `user` is a `project` instruction rather than an `apply`.
  private mutating func depolymorphize(
    polymorphicProjectUser user: AnyInstructionIdentity, with mono: IRFunction.ID,
    passing witnesses: [IRValue], to parameters: [IRParameter], in f: inout IRFunction
  ) {
    let old = f.at(user) as! IRProject

    var xs = witnesses
    lowering(before: user, in: &f) { (e) in
      for (a, p) in zip(old.arguments, parameters) {
        xs.append(e._emitCast(a, to: p.access, p.type))
      }
    }

    let referenceToMono = functionReference(to: mono)
    let s = IRProject(
      callee: referenceToMono, arguments: xs, access: old.access, projectee: old.projectee,
      anchor: old.anchor)

    // Cast the result of the projection if necessary.
    let t = f.result(of: .register(user))!.type
    if !t[.hasGenericParameter] {
      assert(t == f.resolved(s.type)!.type)
      f.replace(user, with: s)
    } else {
      let x = lowering(before: user, in: &f, { $0.insert(s) })!
      f.replace(
        user,
        with: IRPlaceCast(source: x, access: old.access, target: t, anchor: old.anchor))

      var m: [IRValue: Lifetime] = [:]
      f.close(
        IRProject.self, x.register!,
        computingLivenessWith: f.controlFlow(),
        memoizingLifetimesInto: &m)
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
      let d = program.types[p].declaration.map(DeclarationIdentity.init(_:))
      ps.append(.init(type: t, access: .let, declaration: d))
    }

    ps.append(contentsOf: poly.termParameters)
    let mono = IRFunction(
      name: n, anchor: poly.anchor, output: poly.output, typeParameters: [], termParameters: ps)
    return program[module].ir.addFunction(mono)
  }

  /// Emits the existentialized definition of `poly` into its existentialized form, adding the
  /// latter to the module if necessary.
  ///
  /// `poly` is a polymorphic function whose implementation is defined in the current module. Its
  /// existentialized form has not been defined yet, although it may have been declared.
  internal mutating func existentialize(_ poly: IRFunction) {
    let m = demandExistentialized(poly)
    existentialize(poly, into: m)
  }

  /// Emits the existentialized definition of `poly` into `m`.
  ///
  /// `poly` is a polymorphic function whose implementation is defined in the current module and
  /// `mono` identifies the existentialized form of this function and has not been defined yet.
  internal mutating func existentialize(_ poly: IRFunction, into mono: IRFunction.ID) {
    var target = program[module].ir[mono].move()
    assert(poly.isDefined && !target.isDefined, "existentialization already completed")

    /// The type parameters of the function being existentialized.
    let parameters = poly.typeParameters

    /// A table mapping type parameters from the source to their corresponding term parameters in
    /// the existentialized translation.
    var witnesses: [AnyTypeIdentity: IRValue] = .init(
      uniqueKeysWithValues: parameters.enumerated().map({ (i, p) in (p.erased, .parameter(i)) }))

    /// A table for rewriting instructions.
    var properties = IRSubstitutionTable()
    for b in poly.blocks.addresses {
      properties[b] = target.addBlock()
    }
    for i in poly.termParameters.indices {
      properties[IRValue.parameter(i)] = .parameter(i + parameters.count)
    }

    // Iterate over the basic blocks in such a way that definitions are visited before their uses.
    let dominance = DominatorTree(function: poly, controlFlow: poly.controlFlow())
    for b in dominance {
      for i in poly.instructions(in: b) {
        // Copy the instruction if it does not use a generic type requiring a witnessed. Otherwise,
        // replace the instruction with one taking a run-time type witness.
        lowering(.end(of: properties[b]), anchoredTo: poly.at(i).anchor, in: &target) { (me) in
          switch poly.tag(of: i) {
          case IRAlloca.self:
            let s = poly.at(i) as! IRAlloca
            let t = s.storage
            if let w = me._emitTypeWitnessIfGeneric(t, in: poly, reusing: &witnesses) {
              properties[.register(i)] = me._alloca(w, as: t, alignment: s.alignment)
            } else {
              properties[.register(i)] = me.insert(s)!
            }

          case IRProperty.self:
            let s = poly.at(i) as! IRProperty
            let t = poly.result(of: s.record)!.type
            if let w = me._emitTypeWitnessIfGeneric(t, in: poly, reusing: &witnesses) {
              properties[.register(i)] = me._property(
                s.property, of: s.record, as: s.propertyType, computingLayoutWith: w)
            } else {
              properties[.register(i)] = me.insert(s)!
            }

          default:
            let s = poly.at(i)
            if let clone = me.insert(s.substituting(properties)) {
              properties[.register(i)] = clone
            }
          }
        }
      }
    }

    depolymorphize(&target, passing: witnesses)
    program[module].ir[mono].take(definition: target)
  }

  /// Generates IR for accessing a run-time witness of `t` iff it is a generic type, caching
  /// results into `witnesses`; otherwise, returns `nil` without mutating anything.
  ///
  /// `t` is a type occurring in the context of `poly`, which is the function being existentialized
  /// into `self.currentFunction`. `t` is generic if it contains generic type parameter that occur
  /// free. These parameters are expected to be defined by `poly` and assigned in `witnesses`.
  private mutating func _emitTypeWitnessIfGeneric(
    _ t: AnyTypeIdentity, in poly: IRFunction, reusing witnesses: inout [AnyTypeIdentity: IRValue]
  ) -> IRValue? {
    if program.types.seenAsTraitApplication(t) != nil { return nil }

    let ps = program.types.parameters(freeIn: t)
    assert(ps.allSatisfy(poly.typeParameters.contains(_:)))

    // Nothing to do if `t` is not generic.
    if ps.isEmpty {
      return nil
    } else {
      return _emitTypeWitness(of: t, reusing: &witnesses)
    }
  }

}

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
      case IRWitnessTable.self:
        depolymorphize(f.castUnchecked(i, to: IRWitnessTable.self), in: &f, reusing: &witnesses)
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

  /// Replaces uses of `i` its existentialized form.
  private mutating func depolymorphize(
    _ i: IRWitnessTable.ID, in f: inout IRFunction,
    reusing witnesses: inout [AnyTypeIdentity: IRValue]
  ) {
    // Nothing to do if the witness table isn't generic.
    let s = f.at(i)
    if s.arguments.isEmpty { return }
    unimplemented(if: !s.captures.isEmpty, "captures in generic witness table")

    let ws = lowering(before: i.erased, in: &f) { (me) in
      me._emitAccessTypeWitnesses(for: s.arguments, reusing: &witnesses)
    }

    let entries = s.entries.map { (e) in
      // Is the entry implementing a function requirement?
      guard case .function(let n, _) = e else { return e }

      // Is the entry polymorphic?
      let maybePoly = program[module].ir[program[module].ir.identity(function: n)!]
      if !maybePoly.isMonomorphic {
        let p = definePartialApplicationExistentializing(maybePoly)
        return functionReference(to: p)
      } else {
        return e
      }
    }

    let new = IRWitnessTable(
      instantiatedWith: [:], aggregating: entries, capturing: ws,
      as: s.witnessType,
      at: s.anchor)
    f.replace(i.erased, with: new)
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
    let ws = lowering(before: i.erased, in: &f) { (me) in
      me._emitAccessTypeWitnesses(for: application.arguments, reusing: &witnesses)
    }

    // Update the uses of the type application.
    for u in f.uses[.register(i.erased)]! {
      switch f.tag(of: u.user) {
      case IRApply.self where u.index == 0:
        // `i` is used as a callee in an ordinary function application.
        depolymorphize(
          polymorphicApplyUser: u.user, with: mono,
          passing: ws, to: poly.signature.termParameters, in: &f)

      case IRProject.self where u.index == 0:
        depolymorphize(
          polymorphicProjectUser: u.user, with: mono,
          passing: ws, to: poly.signature.termParameters, in: &f)

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
      minimumCapacity: poly.signature.typeParameters.count + poly.signature.termParameters.count)
    let t = program.types.demand(TypeWitness()).erased
    for p in poly.signature.typeParameters {
      let d = program.types[p].declaration.map(DeclarationIdentity.init(_:))
      ps.append(.init(type: t, access: .let, declaration: d))
    }

    ps.append(contentsOf: poly.signature.termParameters)
    let s = IRFunction.Signature(
      typeParameters: [], termParameters: ps, output: poly.signature.output)
    let mono = IRFunction(name: n, anchor: poly.anchor, signature: s)
    return program[module].ir.addFunction(mono)
  }

  /// Returns a partial application of `poly`, which is the generic interface of an implementation
  /// stored in a witness table, to the type arguments captured by that witness table.
  ///
  /// When a generic conformance declaration is existentialized, the entries stored in the witness
  /// table that is projected must be partially applied to the existentialized arguments to present
  /// the right interface. Consider the following to illustrate:
  ///
  ///     trait P { fun f() }
  ///     given w: <T> => T is P { fun f() {} }
  ///
  /// The implementation of `f` defined in `w` is generic over `T`, meaning that it has to be
  /// existentialized along with `w`. However, the resulting existentialized form takes one more
  /// term parameter than the signature of `f` advertises. Hence, we have to construct another
  /// function reading the argument to this parameter from the captures of the existentialized
  /// witness table, which is passed as the first argument.
  private mutating func definePartialApplicationExistentializing(
    _ poly: IRFunction
  ) -> IRFunction.ID {
    // Existentialize the polymorphic function.
    let mono = demandExistentialized(poly)

    // Declare the function forwarding the call to the existentialized function.
    let types = poly.signature.typeParameters
    let terms = poly.signature.termParameters
    var applied = IRFunction(
      name: .applied(program[module].ir[mono].name, 0), // TODO compute a discriminator
      anchor: poly.anchor,
      signature: .init(typeParameters: [], termParameters: terms, output: poly.signature.output))

    // Define the body of that function.
    let entry = applied.addBlock()
    lowering(.end(of: entry), anchoredTo: poly.anchor, in: &applied) { (me) in
      let t = me.program.types.demand(TypeWitness()).erased
      let u = me.program.types.tuple(of: Array(repeating: t, count: types.count))
      let stash = me._witness_table_stash(of: .parameter(0), as: u)

      let callee = me.functionReference(to: mono)
      var arguments: [IRValue] = []
      for i in 0 ..< types.count { arguments.append(me._subfield(stash, at: [i])) }
      for i in 0 ..< terms.count { arguments.append(.parameter(i)) }

      if poly.isSubscript {
        unimplemented()
      } else {
        let r = arguments.removeLast()
        me._apply(callee, arguments, into: r, argumentAccesses: .formAndClose)
      }
      me._return()
    }

    return program[module].ir.addFunction(applied)
  }

  /// Emits the existentialized definition of `poly` into its existentialized form, adding the
  /// latter to the module if necessary.
  ///
  /// `poly` is a polymorphic function whose implementation is defined in the current module. Its
  /// existentialized form has not been defined yet, although it may have been declared.
  internal mutating func existentialize(_ poly: IRFunction) {
    let mono = demandExistentialized(poly)
    existentialize(poly, into: mono)
  }

  /// Emits the existentialized definition of `poly` into `m`.
  ///
  /// `poly` is a polymorphic function whose implementation is defined in the current module and
  /// `mono` identifies the existentialized form of this function and has not been defined yet.
  internal mutating func existentialize(_ poly: IRFunction, into mono: IRFunction.ID) {
    var target = program[module].ir[mono].move()
    assert(poly.isDefined && !target.isDefined, "existentialization already completed")

    /// The type parameters of the function being existentialized.
    let parameters = poly.signature.typeParameters

    /// A table mapping type parameters from the source to their corresponding term parameters in
    /// the existentialized translation.
    var witnesses: [AnyTypeIdentity: IRValue] = .init(
      uniqueKeysWithValues: parameters.enumerated().map({ (i, p) in (p.erased, .parameter(i)) }))

    /// A table for rewriting instructions.
    var properties = IRSubstitutionTable()
    for b in poly.blocks.addresses {
      properties[b] = target.addBlock()
    }
    for i in poly.signature.termParameters.indices {
      properties[IRValue.parameter(i)] = .parameter(i + parameters.count)
    }

    // Iterate over the basic blocks in such a way that definitions are visited before their uses.
    let dominance = DominatorTree(function: poly, controlFlow: poly.controlFlow())
    for b in dominance {
      for i in poly.instructions(in: b) {
        /// Where the next instruction should be inserted.
        let p = InsertionPoint.end(of: properties[b])

        switch poly.tag(of: i) {
        case IRAlloca.self:
          let s = poly.at(i) as! IRAlloca
          lowering(p, anchoredTo: s.anchor, in: &target) { (me) in
            // Gather the generic type parameters that occur free in type of the storage being
            // allocated. They should be defined by the function being existentialized.
            let ps = me.program.types.parameters(freeIn: s.storage)
            assert(ps.allSatisfy(parameters.contains(_:)))

            // If there isn't any generic parameter, we can simply copy the `alloca`. Otherwise,
            // we have to replace it with an `allocx` applied to a run-time type witness.
            if ps.isEmpty {
              properties[.register(i)] = me.insert(s)!
            } else {
              let w = me._emitAccessTypeWitness(of: s.storage, reusing: &witnesses)
              properties[.register(i)] = me._alloca(w, as: s.storage, alignment: s.alignment)
            }
          }

        default:
          let s = poly.at(i)
          lowering(p, anchoredTo: s.anchor, in: &target) { (me) in
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

}

/// Completion queries: the LSP-facing overload-viability machinery.
///
/// These entry points live outside `Typer.swift` so that file stays close to upstream — only
/// visibility relaxations belong there. Everything here delegates judgment to the real solver
/// and resolution machinery rather than reimplementing it.
extension Typer {

  /// Returns the types the argument at `holeIndex` of `call` could be expected to have, unioned over
  /// every overload of the callee that remains viable given the other arguments.
  ///
  /// This drives leading-dot completion in an argument position (`a(.<cursor>)`). A bare implicit
  /// member there is never assigned an expected type by inference — doing so would force a premature
  /// commitment to one overload (see `inferredType(of:Call.ID:)`) — so completion instead asks for
  /// *all* plausible expected types and unions the members reachable on each. An overload is viable
  /// iff the *other* arguments coerce to their corresponding parameters; that judgment is delegated
  /// to the real solver, so disambiguation (`a(., B())`) and conformance/generic matching agree with
  /// what the type checker would accept. The argument types of `call` are read from `self`, which is
  /// assumed already type-checked.
  internal mutating func expectedArgumentTypes(
    at holeIndex: Int, ofCall call: Call.ID, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [AnyTypeIdentity] {
    let arguments = program[call].arguments
    guard holeIndex < arguments.count else { return [] }

    var result: [AnyTypeIdentity] = []
    var seen: Set<AnyTypeIdentity> = []
    for candidate in calleeCandidateTypes(program[call].callee, visibleFrom: scopeOfUse) {
      guard
        let t = expectedHoleType(of: candidate, at: holeIndex, in: call, arguments: arguments)
      else { continue }
      if seen.insert(t).inserted { result.append(t) }
    }
    return result
  }

  /// Returns the possible types of `callee` as the applied expression of a call in `scopeOfUse`.
  private mutating func calleeCandidateTypes(
    _ callee: ExpressionIdentity, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [AnyTypeIdentity] {
    // A name is resolved to its whole overload set, whether or not the checker committed.
    if let n = program.cast(callee, to: NameExpression.self) {
      let name = program[n].name.value
      // Qualified callee (`x.a(...)`): resolve as a member of the qualification's type.
      if let q = program[n].qualification {
        guard
          let qt = program.type(maybeAssignedTo: q), qt != .error, !qt.isVariable,
          !program.types.isMetatype(qt, of: \.isVariable)
        else { return [] }
        return resolve(name, memberOf: qt, visibleFrom: scopeOfUse).map(\.type)
      }
      // Unqualified callee (`a(...)`).
      return resolve(name, unqualifiedIn: scopeOfUse).map(\.type)
    }

    // Any other callee - e.g. a `SyntheticExpression` left where the checker committed to a
    // single candidate and elaborated the callee despite the failing argument — contributes the
    // type the checker assigned to it.
    if let t = program.type(maybeAssignedTo: callee), t != .error { return [t] }
    return []
  }

  /// Returns the parameter type aligned to `holeIndex` if a callee of type `candidate` is viable
  /// for `call` given its other arguments, or `nil` otherwise.
  private mutating func expectedHoleType(
    of candidate: AnyTypeIdentity, at holeIndex: Int,
    in call: Call.ID, arguments: [LabeledExpression]
  ) -> AnyTypeIdentity? {
    var obligations = Obligations()

    // Open generic parameters so they can unify with the argument types. The coercion from the
    // polymorphic type to its opened head makes the solver elaborate the candidate's context —
    // summoning a witness for each of its usings — exactly as `Solver.solve(call:)` does for a
    // real call, so a candidate whose conformance requirements cannot be met is not viable.
    let head: AnyTypeIdentity
    if program.types.contextAndHead(candidate).context.isEmpty {
      head = candidate
    } else {
      let f = program[call].callee
      head = program.types.open(candidate).head
      obligations.assume(
        CoercionConstraint(on: f, from: candidate, to: head, at: program[f].site))
    }

    guard
      program.types.isCallable(head, program[call].style),
      let arrow = program.types.seenAsTermAbstraction(head)
    else { return nil }

    // Align the arguments to the parameters the way `Solver.matches` does: an argument binds to
    // the next parameter iff their labels agree, a skipped parameter must have a default, and
    // every argument must bind. The one extra tolerance is that an *unlabeled* argument also
    // binds a labeled parameter: a value being completed is often unlabeled mid-edit, and when
    // the checker has already elaborated the call, a materialized default carries no label
    // either. Misbindings this permits are still rejected by the coercion check below. A
    // *labeled* argument, however, only binds the parameter carrying that label (`f(y: <hole>)`
    // must not be completed against a defaulted first parameter's type).
    let parameters = program.types[arrow].inputs
    var hole: Parameter? = nil
    var i = 0
    for p in parameters {
      if i < arguments.count,
        (arguments[i].label == nil) || (arguments[i].label?.value == p.label)
      {
        if i == holeIndex {
          hole = p
        } else if let t = program.type(maybeAssignedTo: arguments[i].value), t != .error {
          obligations.assume(
            CoercionConstraint(
              on: arguments[i].value, from: t, to: p.type, reason: .argument,
              at: program.spanForDiagnostic(about: arguments[i].value)))
        }
        i += 1
      } else if p.defaultValue == nil {
        return nil
      }
    }
    guard i == arguments.count, let holeParameter = hole else { return nil }

    var solver = Solver(obligations, withLoggingEnabled: false)
    let solution = solver.solution(using: &self)
    guard !solution.diagnostics.containsError else { return nil }

    let t = program.types.reify(holeParameter.type, applying: solution.substitutions)
    return t == .error ? nil : t
  }

}

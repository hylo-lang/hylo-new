import Utilities

/// The constraint solving algorithm of Hylo's type system.
internal struct Solver {

  /// A typer for querying type relations and resolve names.
  private var typer: Typer! = nil

  /// The score of the best known solution so far.
  private var best: SolutionScore = .worst

  /// The score of the partial solution computed so far.
  private var current: SolutionScore = .zero

  /// The constraints to satisfy.
  private var goals: [any Constraint] = []

  /// A map from goal its outcome.
  private var outcomes: [GoalOutcome] = []

  /// The set of fresh goals.
  private var fresh: [GoalIdentity] = []

  /// The set of goals that can't be solved yet due to missing type assumptions.
  private var stale: [GoalIdentity] = []

  /// The number of root goals.
  private let rootCount: Int

  /// The type and term substitutions made by the solver.
  ///
  /// This map is monotonically extended during constraint solving to assign a type or term to each
  /// open variable in the constraint system. A system is complete if it can be used to derive a
  /// complete substitution map w.r.t. its open variables.
  private var substitutions = SubstitutionTable()

  /// The name binding assumptions made by the solver.
  ///
  /// This map is monotonically extended during constraint solving to assign a declaration to each
  /// unresolved name expression in the constraint system. A system is complete if it can be used
  /// to derive a complete name binding map w.r.t. its unresolved name expressions.
  private var bindings: BindingTable

  private var elaborations: [(ExpressionIdentity, WitnessExpression)] = []

  /// A table from call expression to its arguments after elaboration.
  private var argumentElaborations: [(Call.ID, ParameterBindings)] = []

  /// The current identation level for logging message, or `-1` if logging is disabled.
  private var indentation: Int

  /// Creates an instance for discharging `obligations`, logging a trace of inference steps iff
  /// `loggingIsEnabled` is `true`.
  internal init(_ obligations: Obligations, withLoggingEnabled loggingIsEnabled: Bool) {
    self.bindings = obligations.bindings
    self.rootCount = obligations.constraints.count
    self.indentation = loggingIsEnabled ? 0 : -1
    insert(fresh: obligations.constraints)
  }

  /// Returns a copy of `base` with its `typer` set to `nil`.
  private init (forking base: Self) {
    self = base
    self.typer = nil
  }

  /// The program containing the module being typed.
  internal var program: Program {
    _read { yield typer.program }
    _modify { yield &typer.program }
  }

  /// Returns a solution discharging the goals in `self` using `typer` for querying type relations
  /// and resolve names.
  internal mutating func solution(using typer: inout Typer) -> Solution {
    log("steps:")
    return solution(betterThanOrEqualTo: .worst, using: &typer)!
  }

  /// Returns a solution discharging the goals in `self` with a score better than or equal to
  /// `best` using `typer` for querying type relations and resolve names.
  private mutating func solution(
    betterThanOrEqualTo best: SolutionScore, using typer: inout Typer
  ) -> Solution? {
    self.typer = consume typer
    defer { typer = self.typer.sink() }

    while let g = fresh.popLast() {
      if current > best {
        log("- abort")
        return nil
      } else {
        goals[g].update { (t) in
          self.typer.program.types.reify(t, applying: substitutions, withVariables: .kept)
        }
        log("- solve: " + self.typer.program.show(goals[g]))

        let s = indenting { (me) -> Solution? in
          assert(me.outcomes[g].isPending, "goal already discharged")

          let o: GoalOutcome
          switch me.goals[g] {
          case is EqualityConstraint:
            o = me.solve(equality: g)
          case is CoercionConstraint:
            o = me.solve(coercion: g)
          case is WideningConstraint:
            o = me.solve(widening: g)
          case is ConstructorConversionConstraint:
            o = me.solve(constructorConversion: g)
          case is CallConstraint:
            o = me.solve(call: g)
          case is StaticCallConstraint:
            o = me.solve(staticCall: g)
          case is MemberConstraint:
            o = me.solve(member: g)
          case is OverloadConstraint:
            return me.solve(overload: g)
          default:
            unreachable()
          }

          me.log(outcome: o)
          me.outcomes[g] = o
          if me.outcomes.failed(g) { me.current.errors += 1 }
          return nil
        }

        if let result = s { return result }
      }

      if fresh.isEmpty { refreshCoercionAndWideningConstraints() }
    }

    // Not enough context to solve the remaining stale constraints.
    while let g = stale.popLast() {
      outcomes[g] = .failure { (_, _, _, _) in
        ()  // TODO: Diagnose stale constraints
      }
    }

    assert(goals.indices.allSatisfy({ (g) in !outcomes[g].isPending }))
    return formSolution()
  }

  /// Discharges `g`, which is an equality constraint.
  private mutating func solve(equality g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! EqualityConstraint

    if let s = program.types.unifiable(k.lhs, k.rhs) {
      for (t, u) in s.assignments { assume(t, equals: u) }
      return .success
    } else {
      return .failure { (ss, _, tp, ds) in
        let t = tp.program.types.reify(k.lhs, applying: ss)
        let u = tp.program.types.reify(k.rhs, applying: ss)
        let m = tp.program.format("type '%T' is not compatible with '%T'", [t, u])
        ds.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is a coercion constraint.
  private mutating func solve(coercion g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! CoercionConstraint

    if k.isTrivial {
      return .success
    } else if k.lhs.isVariable {
      return postpone(g)
    }

    // Summon a coercion.
    let es = typer.coerced(k.origin, withType: k.lhs, toMatch: k.rhs)

    // Coercion succeeded?
    if let pick = es.uniqueElement {
      for (t, u) in pick.substitutions.assignments { assume(t, equals: u) }
      if pick.witness.value != .identity(k.origin) {
        let w = program.types.reify(
          pick.witness, applying: pick.substitutions, withVariables: .kept)
        elaborations.append((k.origin, w))
      }
      return .success
    }

    // Coercion failed but there exists a built-in conversion?
    else if program.types.dealiased(k.lhs) == .never {
      let t = program.types.demand(EqualityWitness(lhs: k.lhs, rhs: k.rhs)).erased
      let w = WitnessExpression(
        value: .termApplication(
          .init(builtin: .coercion, type: t),
          .init(value: .identity(k.origin), type: k.lhs)),
        type: .never)
      elaborations.append((k.origin, w))
      return .success
    }

    // Coercion failed but it may succeed with more context?
    else if k.rhs[.hasVariable] {
      return postpone(g)
    }

    // Coercion failed.
    else { return .failure(diagnoseInvalidCoercion(k)) }
  }

  /// Returns the simplification of `k` as an equality between its operands.
  private mutating func simplify(_ k: CoercionConstraint) -> GoalOutcome {
    let e = EqualityConstraint(lhs: k.lhs, rhs: k.rhs, site: k.site)
    let s = schedule(e)
    return .forward([s], diagnoseInvalidCoercion(k))
  }

  /// Returns a function diagnosing a failure to solve a `k` due to an invalid coercion.
  private func diagnoseInvalidCoercion(_ k: CoercionConstraint) -> DiagnoseFailure {
    { (ss, _, tp, ds) in
      let t = tp.program.types.reify(k.lhs, applying: ss)
      let u = tp.program.types.reify(k.rhs, applying: ss)

      switch k.reason {
      case .argument:
        ds.insert(tp.program.cannotPass(argument: t, to: u, at: k.site))

      case .ascription:
        ds.insert(tp.program.doesNotDenoteType(k.origin))

      default:
        let scopeOfUse = tp.program.parent(containing: k.origin)
        let (usings, lhs) = tp.program.types.open(t)
        var notes: [Diagnostic] = []

        if let s = tp.program.types.unifiable(lhs, u) {
          for using in usings {
            let x = tp.program.types.reify(using, applying: s)
            if x[.hasError] { continue }

            let n = tp.summon(x, in: scopeOfUse).count
            if n == 0 {
              notes.append(tp.program.noGivenInstance(of: x, at: k.site).as(.note))
            } else if n > 1 {
              notes.append(tp.program.multipleGivenInstances(of: x, at: k.site).as(.note))
            }
          }
        }

        ds.insert(tp.program.noCoercion(from: t, to: u, at: k.site, because: notes))
      }
    }
  }

  /// Discharges `g`, which is a widening constraint.
  private mutating func solve(widening g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! WideningConstraint

    // Check that the left-hand side can be widened to the right-hand side.
    switch program.types[k.rhs] {
    case is TypeVariable:
      return postpone(g)

    case let u as Sum:
      if k.lhs.isVariable || u.elements.contains(where: \.isVariable) {
        return postpone(g)
      } else {
        fatalError("TODO")
      }

    default:
      return simplify(k)
    }
  }

  /// Discharges `g`, which is a constructor conversion constraint.
  private mutating func solve(constructorConversion g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! ConstructorConversionConstraint

    // Can't do anything before we've inferred the type of the source.
    if k.lhs.isVariable {
      return postpone(g)
    }

    // Is the source an initializer?
    else if let t = program.types.asConstructor(k.lhs) {
      let subgoal = schedule(EqualityConstraint(lhs: k.rhs, rhs: t, site: k.site))
      return delegate([subgoal])
    }

    // The source isn't an initializer.
    else {
      return .failure { (ss, _, tp, ds) in
        let t = tp.program.types.reify(k.lhs, applying: ss)
        let m = tp.program.format("cannot use value of type '%T' as a constructor", [t])
        ds.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Returns the simplification of `k` as an equality between its operands.
  private mutating func simplify(_ k: WideningConstraint) -> GoalOutcome {
    let e = EqualityConstraint(lhs: k.lhs, rhs: k.rhs, site: k.site)
    let s = schedule(e)
    return .forward([s]) { (ss, _, tp, ds) in
      let t = tp.program.types.reify(e.lhs, applying: ss)
      let u = tp.program.types.reify(e.rhs, applying: ss)
      ds.insert(tp.program.noConversion(from: t, to: u, at: e.site))
    }
  }

  /// Discharges `g`, which is a call constraint.
  private mutating func solve(call g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! CallConstraint

    // Can't do anything before we've inferred the type of the callee.
    let (context, head) = program.types.contextAndHead(k.callee)
    if head.isVariable {
      return postpone(g)
    }

    // Callee doesn't have the right shape?
    else if !program.types.isCallable(head, program[k.origin].style) {
      return invalidCallee(k)
    }

    var subgoals: [GoalIdentity] = []
    let coercion: GoalIdentity
    let callee: AnyTypeIdentity

    // Compile-time implicits missing?
    if context.isEmpty {
      coercion = -1
      callee = head
    } else {
      let f = program[k.origin].callee
      (_, callee) = program.types.open(k.callee)
      coercion = schedule(
        CoercionConstraint(on: f, from: k.callee, to: callee, at: program[f].site))
      subgoals.append(coercion)
    }

    // Argument list has the right shape?
    let w = program.types.seenAsCallableAbstraction(callee)!
    guard let (bs, ss, inplace) = matches(k, w) else {
      return .failure { (_, _, tp, ds) in
        ds.insert(tp.program.incompatibleLabels(found: k.labels, expected: w.labels, at: k.site))
      }
    }

    // Infer the output type.
    let m = inplace || program.isMarkedMutating(program[k.origin].callee)
    if let o = program.types.resultOfApplying(callee, mutably: m) {
      subgoals.append(schedule(EqualityConstraint(lhs: o, rhs: k.output, site: k.site)))
    } else {
      assert(program.types.tag(of: callee) == Bundle.self)
      return .failure { (ss, _, tp, ds) in
        let t = tp.program.types.reify(callee, applying: ss)
        let e = tp.program.cannotCall(t, mutably: m, at: tp.program[k.origin].site)
        ds.insert(e)
      }
    }

    if bs.hasDefaulted {
      argumentElaborations.append((k.origin, bs))
    }

    for s in ss {
      subgoals.append(schedule(s))
    }

    return .forward(subgoals) { (substitutions, outcomes, typer, ds) in
      // Diagnose failures to coerce callees first.
      if coercion >= 0, let f = outcomes.diagnosticBuilder(coercion) {
        f(substitutions, outcomes, &typer, &ds)
      } else {
        outcomes.diagnoseFailures(in: subgoals, into: &ds, using: substitutions, &typer)
      }
    }
  }

  /// Returns how the types of the arguments in `k` match the parameters of `f`.
  ///
  /// If the arguments in `k` match, this method returns a triple `(bs, ss, inplace)` where `bs`
  /// maps each parameter of `f` to its value, `ss` contains coercion constraints resulting from
  /// argument passing, and `inplace` is `true` iff at least one of the arguments passed to an
  /// `auto` parameter is  marked for mutation.
  ///
  /// If the arguments in `k` do not match, this method returns `nil`.
  private mutating func matches(
    _ k: CallConstraint, _ f: Callable
  ) -> (bingings: ParameterBindings, subgoals: [CoercionConstraint], inplace: Bool)? {
    var bindings = ParameterBindings()
    var subgoals: [CoercionConstraint] = []

    var inplace = false
    var i = 0
    for p in f.inputs {
      // Is there's an explicit argument with the right label?
      if (k.arguments.count > i) && (k.arguments[i].label == p.label) {
        let v = program[k.origin].arguments[i].value
        let a = k.arguments[i]
        bindings.append(.explicit(i))
        subgoals.append(
          CoercionConstraint(
            on: v, from: a.type, to: p.type, reason: .argument, at: program[v].site))
        i += 1

        // Is the argument mutating an `auto` parameter?
        if (p.access == .auto) && program.isMarkedMutating(v) { inplace = true }
      }

      // The parameter has a default value?
      else if let e = p.defaultValue {
        bindings.append(.defaulted(e))
        continue
      }

      // Arguments do not match.
      else { return nil }
    }

    assert(bindings.elements.count == f.inputs.count)
    return i == k.arguments.count ? (bindings, subgoals, inplace) : nil
  }

  /// Returns a failure to solve a `k` due to an invalid callee type.
  private func invalidCallee(_ k: CallConstraint) -> GoalOutcome {
    .failure { (ss, _, tp, ds) in
      let t = tp.program.types.reify(k.callee, applying: ss)
      let e = tp.program.cannotCall(t, tp.program[k.origin].style, at: tp.program[k.origin].site)
      ds.insert(e)
    }
  }

  /// Discharges `g`, which is a static call constraint.
  private mutating func solve(staticCall g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! StaticCallConstraint
    assert(k.arguments.count == program[k.origin].arguments.count)

    // Can't do anything before we've inferred the type of the callee.
    if k.callee.isVariable {
      return postpone(g)
    }

    // Is the callee a universal type?
    if let u = program.types[k.callee] as? UniversalType {
      if u.parameters.count != k.arguments.count {
        return invalidArgumentCount(k, expected: u.parameters.count)
      }

      let ss = TypeArguments(mapping: u.parameters, to: k.arguments)
      let t = program.types.substitute(ss, in: u.body)
      let subgoal = schedule(EqualityConstraint(lhs: k.output, rhs: t, site: k.site))
      return delegate([subgoal])
    }

    // Is the callee a higher-kinded type parameter?
    if let u = program.types.cast(k.callee, to: GenericParameter.self) {
      let parameters = program.types.parameters(of: u)
      if parameters.count != k.arguments.count {
        return invalidArgumentCount(k, expected: parameters.count)
      }

      let ss = TypeArguments(mapping: parameters, to: k.arguments)
      let t = program.types.demand(TypeApplication(abstraction: u.erased, arguments: ss)).erased
      let subgoal = schedule(EqualityConstraint(lhs: k.output, rhs: t, site: k.site))
      return delegate([subgoal])
    }

    // The callee is not application.
    return invalidArgumentCount(k, expected: 0)
  }

  /// Returns a failure to solve a `k` due to an invalid number of arguments.
  private func invalidArgumentCount(
    _ k: StaticCallConstraint, expected: Int
  ) -> GoalOutcome {
    .failure { (ss, _, tp, ds) in
      let f = if let n = tp.program.cast(tp.program[k.origin].callee, to: NameExpression.self) {
        "'\(tp.program[n].name)'"
      } else {
        tp.program.format("value of type '%T'", [tp.program.types.reify(k.callee, applying: ss)])
      }

      let m = if expected == 0 {
        "\(f) takes no compile-time arguments"
      } else {
        "\(f) takes \(expected) compile-time argument(s); found \(k.arguments.count)"
      }

      ds.insert(
        .init(.error, m, at: tp.program.spanForDiagnostic(about: tp.program[k.origin].callee)))
    }
  }

  /// Discharges `g`, which is a member constraint.
  private mutating func solve(member g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! MemberConstraint

    // Can't do anything before we've inferred the type of the qualification.
    if k.qualification.isVariable || program.types.isMetatype(k.qualification, of: \.isVariable) {
      return postpone(g)
    }

    let n = program[k.member].name
    let candidates = typer.resolve(
      n.value, memberOf: k.qualification, visibleFrom: program.parent(containing: k.member))

    if candidates.isEmpty {
      return .failure { (ss, _, tp, ds) in
        let t = tp.program.types.reify(k.qualification, applying: ss)
        ds.insert(tp.program.undefinedSymbol(tp.program[k.member].name, memberOf: t))
      }
    }

    var o = Obligations()
    switch typer.assume(k.member, boundTo: candidates, for: k.role, at: k.site, in: &o) {
    case .left(let t):
      bindings.merge(o.bindings, uniquingKeysWith: { (_, _) in unreachable() })
      var subgoals = [schedule(EqualityConstraint(lhs: t, rhs: k.type, site: k.site))]
      subgoals.append(contentsOf: o.constraints.map({ (c) in schedule(c) }))
      return delegate(subgoals)

    case .right(let e):
      return .failure { (_, _, _, d) in d.insert(e) }
    }
  }

  /// Discharges `g`, which is an overload constraint.
  private mutating func solve(overload g: GoalIdentity) -> Solution {
    let k = goals[g] as! OverloadConstraint

    var viable: [(choice: NameResolutionCandidate, solution: Solution)] = []
    for choice in k.candidates {
      let equality = EqualityConstraint(lhs: k.type, rhs: choice.type, site: k.site)
      log("- pick: \(program.show(equality))")

      let s = indenting { (me) in
        var fork = Self(forking: me)
        let subgoal = fork.insert(fresh: equality)
        fork.outcomes[g] = fork.delegate([subgoal])
        fork.bindings[k.name] = choice.reference
        return fork.solution(betterThanOrEqualTo: me.best, using: &me.typer)
      }

      if let newSolution = s {
        let newScore = SolutionScore(
          errors: newSolution.diagnostics.elements.count, penalties: current.penalties)

        if newScore < best {
          best = newScore
          viable = [(choice, newSolution)]
        } else {
          viable.append((choice, newSolution))
        }
      }
    }

    let scopeOfUse = program.parent(containing: k.name)
    let least = viable.least { (a, b) in
      program.isPreferred(a.choice, other: b.choice, in: scopeOfUse)
    }

    if let (_, s) = least {
      return s
    } else {
      // There must be at least one solution.
      var s = viable[0].solution
      s.add(.init(.error, "ambiguous use of '\(program[k.name].name.value)'", at: k.site))
      return s
    }
  }

  /// Creates a solution with the current state.
  private mutating func formSolution() -> Solution? {
    if current > best { return nil }

    let ss = substitutions.optimized()
    var ds = DiagnosticSet()

    for g in 0 ..< rootCount {
      if let f = outcomes.diagnosticBuilder(g) {
        f(ss, outcomes, &typer, &ds)
      }
    }

    return Solution(
      substitutions: ss,
      bindings: bindings,
      elaborations: elaborations,
      argumentElaborations: argumentElaborations,
      diagnostics: ds)
  }

  /// Assumes that `n` refers to `r`.
  private mutating func assume(_ n: NameExpression.ID, boundTo r: DeclarationReference) {
    bindings[n] = r
  }

  /// Assumes that `t` is assigned to `u`.
  private mutating func assume(_ t: TypeVariable.ID, equals u: AnyTypeIdentity) {
    log("- assume: " + program.format("%T = %T", [t.erased, u]))
    substitutions.assign(u, to: t)
    refresh()
  }

  /// Refresh constraints containing type variables that have been assigned.
  private mutating func refresh() {
    // Nothing to do if the stale set is empty.
    if stale.isEmpty { return }

    var end = stale.count
    for i in (0 ..< stale.count).reversed() {
      var changed = false
      goals[stale[i]].update { (t) in
        let u = typer.program.types.reify(t, applying: substitutions, withVariables: .kept)
        if t != u { changed = true }
        return u
      }

      if changed {
        log("- refresh: " + program.show(goals[stale[i]]))
        fresh.append(stale[i])
        stale.swapAt(i, end - 1)
        end -= 1
      }
    }
    stale.removeSubrange(end...)
  }

  /// Transforms all stale coercion and widening constraints into equality constraints, selecting
  /// upper/lower bounds using to the current type assignments.
  private mutating func refreshCoercionAndWideningConstraints() {
    // Nothing to do if the stale set is empty.
    if stale.isEmpty { return }

    var end = stale.count
    for i in (0 ..< stale.count).reversed() {
      switch goals[stale[i]] {
      case let k as CoercionConstraint:
        outcomes[stale[i]] = simplify(k)
      case let k as WideningConstraint:
        outcomes[stale[i]] = simplify(k)
      default:
        continue
      }
      stale.swapAt(i, end - 1)
      end -= 1
    }

    stale.removeSubrange(end...)
  }

  /// Inserts `gs` into the fresh set and return their identities.
  @discardableResult
  private mutating func insert<T: Collection<any Constraint>>(fresh gs: T) -> [GoalIdentity] {
    gs.reversed().map({ (g) in insert(fresh: g) })
  }

  /// Inserts `k` into the fresh set and returns its identity.
  private mutating func insert(fresh k: any Constraint) -> GoalIdentity {
    let g = goals.count
    goals.append(k)
    if k.isTrivial && false {
      outcomes.append(.success)
    } else {
      outcomes.append(.pending)
      fresh.append(g)
    }
    return g
  }

  /// Schedules `k` to be solved in the future and returns its identity.
  private mutating func schedule(_ k: Constraint) -> GoalIdentity {
    log("- schedule: \(program.show(k))")
    return insert(fresh: k)
  }

  /// Reschedules `g` to be solved once the solver has inferred more information about at least one
  /// of the free variables occuring in `g`.
  private mutating func postpone(_ g: GoalIdentity) -> GoalOutcome {
    stale.append(g)
    return .pending
  }

  /// Returns the splitting of a goal into `subgoals`, reporting each of failure individually.
  private func delegate(_ subgoals: [GoalIdentity]) -> GoalOutcome {
    .forward(subgoals) { (substitutions, outcomes, typer, diagnostics) in
      outcomes.diagnoseFailures(in: subgoals, into: &diagnostics, using: substitutions, &typer)
    }
  }

  /// Returns the result of calling `action` on a projection of `self` where `identation` has been
  /// incremented if logging is enabled.
  private mutating func indenting<T>(_ action: (inout Self) -> T) -> T {
    if indentation < 0 {
      return action(&self)
    } else {
      indentation += 1
      defer { indentation -= 1 }
      return action(&self)
    }
  }

  /// Logs a line of text to the standard output iff logging is enabled.
  private func log(_ line: @autoclosure () -> String) {
    if indentation < 0 { return }
    print(String(repeating: "  ", count: indentation) + line())
  }

  /// Logs `o` to the standard output iff loggig is enabled.
  private func log(outcome o: GoalOutcome) {
    log({
      switch o {
      case .pending: "- defer"
      case .success: "- ok"
      case .failure: "- fail"
      case .forward: "- forward"
      }
    }())
  }

}

/// A closure reporting diagnostics of a goal's failure into `ds`, using `ss` to reify types that
/// are defined in the program typed by `tp`, and reading the outcome of other goals from `os`.
private typealias DiagnoseFailure = (
  _ ss: SubstitutionTable,
  _ os: [GoalOutcome],
  _ tp: inout Typer,
  _ ds: inout DiagnosticSet
) -> Void

/// The identity of a goal.
private typealias GoalIdentity = Int

/// The outcome of a goal.
private enum GoalOutcome {

  /// The goal hasn't been processed yet.
  case pending

  /// The goal was discharged.
  case success

  /// The goal was unsatisfiable.
  ///
  /// The payload contains a function producing a diagnostic of the failure.
  case failure(DiagnoseFailure)

  /// The goal was split into sub-goals.
  ///
  /// The payload contains the identity of the sub-goals and a function producing a diagnostic of
  /// the failure in case one of the sub-goals is unsatisfiable.
  case forward([GoalIdentity], DiagnoseFailure)

  /// `true` iff `self` is `.pending`
  var isPending: Bool {
    if case .pending = self { true } else { false }
  }

}

extension [GoalOutcome] {

  /// Returns `true` iff `g` has failed.
  fileprivate func failed(_ g: GoalIdentity) -> Bool {
    switch self[g] {
    case .failure:
      return true
    case .forward(let gs, _):
      return gs.contains(where: failed(_:))
    default:
      return false
    }
  }

  /// If `g` has failed, returns the function producing its diagnostic.
  fileprivate func diagnosticBuilder(_ g: GoalIdentity) -> DiagnoseFailure? {
    switch self[g] {
    case .pending, .success:
      return nil
    case .failure(let f):
      return f
    case .forward(let gs, let f):
      return gs.contains(where: failed(_:)) ? f : nil
    }
  }

  /// Calls the diagnostic builder of all the failed goals in `gs` with the given arguments.
  fileprivate func diagnoseFailures<S: Sequence<GoalIdentity>>(
    in gs: S, into ds: inout DiagnosticSet,
    using substitutions: SubstitutionTable, _ typer: inout Typer
  ) {
    for g in gs {
      if let f = diagnosticBuilder(g) {
        f(substitutions, self, &typer, &ds)
      }
    }
  }

}

/// A value measuring the correctness of a solution.
private struct SolutionScore {

  /// The raw value of the score.
  private var rawValue: UInt64

  /// Creates an instance with the given raw value.
  private init(rawValue: UInt64) {
    self.rawValue = rawValue
  }

  /// Creates an instance with the given properties.
  fileprivate init(errors: Int, penalties: Int) {
    assert(errors < UInt32.max && penalties < UInt32.max)
    self.rawValue = UInt64(errors) << 32 | UInt64(penalties)
  }

  /// The number of unsatisfiable root goals.
  fileprivate var errors: Int {
    get { Int(truncatingIfNeeded: rawValue >> 32) }
    set { self.rawValue = UInt64(newValue) << 32 | UInt64(penalties) }
  }

  /// The number of penalties associated with the solution.
  fileprivate var penalties: Int {
    get { Int(truncatingIfNeeded: rawValue & ((1 << 32) - 1)) }
    set { self.rawValue = UInt64(errors) << 32 | UInt64(newValue) }
  }

  /// The best possible score.
  fileprivate static var zero: SolutionScore { .init(rawValue: 0) }

  /// The worst possible score.
  fileprivate static var worst: SolutionScore { .init(rawValue: .max) }

}

extension SolutionScore: Comparable {

  internal static func < (l: Self, r: Self) -> Bool {
    l.rawValue < r.rawValue
  }

}

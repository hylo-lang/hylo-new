import Utilities

extension IRFunction {

  /// The state of inlining.
  internal struct InliningContext {

    /// The functions whose contents are being inlined.
    fileprivate var stack: [IRFunction.Name]

    /// Creates an empty instance.
    internal init() {
      self.stack = []
    }

  }

  /// The outcome of an attempt to inline the application of a subscript or function.
  private enum InlningResult {

    /// Inlining succeeded
    case success

    /// Inlining did not occur because the definition of the callee could not be resolved.
    case skipped

    /// Inlining did not occur because of recursion.
    case recursion

  }

  /// If `self` is exposed and must be inlined, verifies that it only uses exposed symbols.
  internal func upholdInliningRequirements(in m: Module.ID, using typer: inout Typer) -> Bool {
    // Nothing to do unless inlining is mandated and the function is exposed.
    if typer.program.inliningPolicy(of: name) != .always { return true }
    if typer.program.isPrivate(name, in: m) { return true }

    var success = true
    for i in instructions() {
      if let s = at(i) as? IRApply, case .function(let f, _) = s.callee {
        if typer.program.isPrivate(f, in: m) {
          let a = typer.program.span(s.anchor)
          let d = Diagnostic(.error, "use of non-exposed function in inlined function", at: a)
          typer.program[m].addDiagnostic(d)
          success = false
        }
      }
    }

    return success
  }

  /// Inlines the contents of the callees in `self` that were resolved statically to a declaration
  /// that should be inlined given `context`.
  internal mutating func inlineSimpleCallees(
    emittingInto m: Module.ID, using typer: inout Typer,
    in context: inout InliningContext
  ) {
    // Nothing to do if the function already went through mandatory inlining.
    if passedMandatoryInlining { return }

    context.stack.append(name)
    defer { context.stack.removeLast() }

    for b in blocks {
      // Nothing to do if the block's empty.
      guard var j = b.last else { continue }

      // Look for calls to inline. `j` ranges over the identities of the block in reverse order so
      // that we can set `i` to the instruction immediately before any split necessary to inline
      // the contents of another function.
      while j != b.first {
        var i = instruction(before: j)!
        defer { swap(&i, &j) }

        // TODO: Subscripts
        if let k = cast(j, to: IRApply.self) {
          switch inlineApply(k, emittingInto: m, using: &typer, in: &context) {
          case .recursion:
            let d = typer.program.notInlinable(dueToRecursiveCall: j, in: self)
            typer.program[m].addDiagnostic(d)
            return

          default:
            break
          }
        }
      }
    }

    // Inlining may have inserted calls to never-returning functions, introducing unreachable basic
    // blocks that have to be eliminated.
    removeCodeAfterNeverReturningCalls()
    removeUnreachableBlocks()

    // Mandatory inlining is done.
    setMandatoryInliningPassed()
  }

  /// Substitutes `i` with the contents of its callee if the latter has been statically resolved to
  /// a declaration that should be inlined given `context`.
  private mutating func inlineApply(
    _ i: IRApply.ID, emittingInto m: Module.ID, using typer: inout Typer,
    in context: inout InliningContext
  ) -> InlningResult {
    let s = at(i)
    guard case .function(let callee, _) = s.callee else { return .skipped }

    // Should the callee be inlined?
    if !typer.program.shouldInline(callee) { return .skipped }

    // Locate the definition of `f`.
    guard let (n, f) = typer.program.definition(of: callee, visibleFrom: m) else {
      // Either the callee is not defined, in which case an error has been reported elsewhere, or
      // it is being inlined, in which case we must complain about recursive inlining.
      if context.stack.contains(callee) {
        return .recursion
      } else {
        return .skipped
      }
    }

    // Should the callee go through mandatory inlining first?
    if !typer.program[n].ir[f].passedMandatoryInlining {
      var g = typer.program[n].ir[f].move()
      g.inlineSimpleCallees(emittingInto: n, using: &typer, in: &context)
      typer.program[n].ir[f].take(definition: g)
    }

    // Make sure the functions used in the callee are declared in `m`. These functions should be
    // either defined in `m` or exposed from another module.
    let source = typer.program[n].ir[f]
    for k in source.instructions() {
      for case .function(let f, _) in source.at(k).operands {
        typer.program[m].ir.declare(typer.program[n].ir.functions[f]!)
      }
    }

    // Construct a table mapping each parameter to its argument.
    var table = IRSubstitutionTable()
    table[source.returnRegister!] = s.result
    for (p, a) in s.arguments.enumerated() {
      table[.parameter(p)] = a
    }

    // Replace the call with the contents of the callee.
    typer.program.withEmitter(insertingIn: m) { (emitter) in
      emitter.insert(
        contentsOf: source, before: i.erased, in: &self,
        substitutingOperandsWith: table)
    }
    remove(i.erased)

    return .success
  }

}

extension Program {

  /// Returns the conditions under which the body of `f` should be inlined.
  fileprivate func inliningPolicy(of f: IRFunction.Name) -> InliningPolicy {
    switch f {
    case .lowered(let d):
      return inliningPolicy(of: d) ?? .opportunistic
    default:
      return .opportunistic
    }
  }

  /// Returns the conditions under which the body of `f` should be inlined, if defined.
  fileprivate func inliningPolicy(of d: DeclarationIdentity) -> InliningPolicy? {
    switch tag(of: d) {
    case FunctionDeclaration.self:
      return .some(self[castUnchecked(d, to: FunctionDeclaration.self)].inliningPolicy)
    default:
      return .none
    }
  }

  /// Returns `true` iff `f` refers to a declaration annotated with `@inline(always)`.
  fileprivate func shouldInline(_ f: IRFunction.Name) -> Bool {
    inliningPolicy(of: f) == .always
  }

}

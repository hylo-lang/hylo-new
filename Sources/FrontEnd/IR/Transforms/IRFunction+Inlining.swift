extension IRFunction {

  /// If `self` is exposed and must be inlined, verifies that it only uses exposed symbols.
  internal func upholdInliningRequirements(in m: Module.ID, using typer: inout Typer) -> Bool {
    // Nothing to do unless inlining is mandated and the function is exposed.
    if typer.program.inliningPolicy(of: name) != .always { return true }
    if typer.program.isPrivate(name, in: m) { return true }

    var success = true
    for i in instructions() {
      if let s = at(i) as? IRApply, case .function(let f, _) = s.callee {
        if typer.program.isPrivate(f, in: m) {
          let d = Diagnostic(
            .error, "use of non-exposed function in inlined function", at: s.anchor.site)
          typer.program[m].addDiagnostic(d)
          success = false
        }
      }
    }

    return success
  }

  /// Inlines the contents of the callees in `self` that have been resolved statically to a
  /// declaration annotated with `@inline(always)`.
  internal mutating func inlineSimpleCallees(emittingInto m: Module.ID, using typer: inout Typer) {
    var work = Array(blocks)
    while let b = work.popLast() {
      // Nothing to do if the block's empty.
      guard var i = b.first else { continue }

      // Look for calls to inline.
      while i != b.last {
        var j = instruction(after: i)!

        if let s = at(i) as? IRApply, case .function(let f, _) = s.callee {
          // Should the callee be inlined?
          let callee = typer.program[m].ir.functions[f]!
          if !callee.isDefined || !typer.program.shouldInline(callee.name) { break }

          // Construct a table mapping each parameter to its argument.
          var table = IRSubstitutionTable()
          table[callee.returnRegister!] = s.result
          for (p, a) in s.arguments.enumerated() {
            table[.parameter(p)] = a
          }

          // Replace the call with the contents of the callee.
          remove(i)
          typer.program.withEmitter(insertingIn: m) { (emitter) in
            emitter.insert(
              contentsOf: callee, before: j, in: &self,
              substitutingOperandsWith: table)
          }
        }

        swap(&i, &j)
      }
    }
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

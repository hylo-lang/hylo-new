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
  /// annotated with `@inline(always)`, and whose definition is visible from `m`.
  internal mutating func inlineSimpleCallees(emittingInto m: Module.ID, using typer: inout Typer) {
    var work = Array(blocks)
    while let b = work.popLast() {
      // Nothing to do if the block's empty.
      guard var j = b.last else { continue }

      // Look for calls to inline. `j` ranges over the identities of the block in reverse order so
      // that we can set `i` to the instruction immediately before any split necessary to inline
      // the contents of another function.
      while j != b.first {
        var i = instruction(before: j)!
        defer { swap(&i, &j) }

        // TODO: Subscripts
        if let s = at(j) as? IRApply, case .function(let f, _) = s.callee {
          // Should the callee be inlined?
          let callee = typer.program[m].ir.functions[f]!.name
          if !typer.program.shouldInline(callee) { continue }

          // Can we access the callee's definition.
          guard let (n, source) = typer.program.definition(of: callee, visibleFrom: m) else {
            continue
          }

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
              contentsOf: source, before: j, in: &self, substitutingOperandsWith: table)
          }
          remove(j)
        }
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

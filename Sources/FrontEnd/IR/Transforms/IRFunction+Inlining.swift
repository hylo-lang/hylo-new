extension IRFunction {

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

        if let s = at(i) as? IRApply, case .function(let f, _, _) = s.callee {
          // Should the callee be inlined?
          let callee = typer.program[m].ir[f]
          if !callee.isDefined || !typer.program.shouldInline(callee.name, in: m) { break }

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
              substitutingOperandsWith: table,
              computingAnchorsWith: { (f, k) in f.at(k).anchor })
          }
        }

        swap(&i, &j)
      }
    }
  }

}

extension Program {

  /// Returns `true` iff `f` refers to a declaration annotated with `@inline(always)`.
  fileprivate func shouldInline(_ f: IRFunction.Name, in m: Module.ID) -> Bool {
    switch f {
    case .lowered(let d):
      return shouldInline(d, in: m)
    default:
      return false
    }
  }

  /// Returns `true` iff `d` is a declaration annotated with `@inline(always)`.
  fileprivate func shouldInline(_ d: DeclarationIdentity, in m: Module.ID) -> Bool {
    switch tag(of: d) {
    case FunctionDeclaration.self:
      return shouldInline(castUnchecked(d, to: FunctionDeclaration.self), in: m)
    default:
      return false
    }
  }

  /// Returns `true` iff `d` is a declaration annotated with `@inline(always)`.
  fileprivate func shouldInline(_ d: FunctionDeclaration.ID, in m: Module.ID) -> Bool {
    switch tag(of: d) {
    case FunctionDeclaration.self:
      if let a = annotation("inline", appliedTo: d) {
        return InliningPolicy(a) == .always
      } else {
        return false
      }

    default:
      return false
    }
  }

}

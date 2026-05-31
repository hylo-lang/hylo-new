extension IRFunction {

  /// Elaborates `self` to use regular function calls, if `self` is a projection caller.
  internal mutating func elaborateProjectionCaller(emittingInto m: Module.ID, using typer: inout Typer) {
    // Nothing to do if the function isn't defined.
    if !isDefined { return }

    // Determine the `IRProject` calls.
    let projectCalls = instructions().filter { tag(of: $0) == IRProject.self }
    guard !projectCalls.isEmpty else { return }

    // Demand the plateau functions.
    typer.program.withEmitter(insertingIn: m) { (emitter) in
      for (index, call) in projectCalls.enumerated() {
        let p = at(call) as! IRProject
        _ = emitter.demandPlateau(for: self, index: index, projectedType: p.projectee)
      }
    }
    // TODO: continue with the implementation.
  }

}

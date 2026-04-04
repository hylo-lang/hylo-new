extension IRFunction {

  /// Eliminates type application from `self`, which is a monomorphic function, using either
  /// existentialization or monomorphization.
  internal mutating func depolymorphize(emittingInto m: Module.ID, using typer: inout Typer) {
    // Nothing to do if the function is generic; depolymorphization starts with the monomorphic
    // roots of the call graph.
    if !isMonomorphic { return }

    typer.program.withEmitter(insertingIn: m) { (emitter) in
      emitter.depolymorphize(&self)
    }
  }

}

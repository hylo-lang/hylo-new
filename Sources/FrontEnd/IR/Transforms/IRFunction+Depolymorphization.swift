extension IRFunction {

  /// If `self` is monomorphic, eliminates the type applications occurring in its implementation
  /// using either existentialization or monomorphization.
  ///
  /// Polymorphic functions are depolymorphized on demand iff they are exposed or they are called
  /// by another depolymorphized function.
  internal mutating func depolymorphize(emittingInto m: Module.ID, using typer: inout Typer) {
    assert(isDefined)
    if !isMonomorphic { return }

    typer.program.withEmitter(insertingIn: m) { (emitter) in
      emitter.depolymorphize(&self)
    }
  }

  /// If `self` is polymorphic and also exposed, generates its existentialized form.
  ///
  /// Generic functions exposed to a module's ABI are guaranteed to provide an existentialized
  /// implementation that can be linked without monomorphization.
  internal mutating func existentializeIfExposed(
    emittingInto m: Module.ID, using typer: inout Typer
  ) {
    assert(isDefined)
    if isMonomorphic || !typer.program.isPrivate(name, in: m) { return }

    typer.program.withEmitter(insertingIn: m) { (emitter) in
      emitter.existentialize(self)
    }
  }

}

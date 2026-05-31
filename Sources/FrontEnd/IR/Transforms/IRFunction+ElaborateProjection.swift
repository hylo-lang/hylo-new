extension IRFunction {

  /// Elaborates `self` into ramp + slide functions, if `self` is a projection.
  ///
  /// A projection is always divided into two "segments":
  ///  - The ramp, which contains the instructions that must be executed before the `yield`.
  ///  - The slide, which contains the instructions that must be executed after the `yield`.
  ///
  /// After this call, the original projection functions are removed from the program, and replaced
  /// by the corresponding ramp and slide functions. The ramps and slides are generated in the same
  /// module as the original projection.
  ///
  /// If there are instructions in the ramp that are used in the slide, they are materialized into a
  /// frame that is passed from the ramp to the slide.
  internal mutating func elaborateProjection(emittingInto m: Module.ID, using typer: inout Typer) {
    // Nothing to do if the function isn't a subscript or isn't defined.
    if !isSubscript || !isDefined { return }

    // Demand the ramp and slide functions.
    typer.program.withEmitter(insertingIn: m) { (emitter) in
      _ = emitter.demandProjectionRamp(for: self)
      _ = emitter.demandProjectionSlide(for: self)
    }
    // TODO: continue with the implementation.
  }

}

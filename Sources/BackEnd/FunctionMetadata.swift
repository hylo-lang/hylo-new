import SwiftyLLVM

/// Information about the LLVM representation of a function compiled from Hylo.
internal struct FunctionMetadata {

  /// The type of the function and the way it relates to its counterpart in Hylo.
  internal let prototype: Prototype

  /// The declaration (and possibly definition) of the function.
  internal let value: SwiftyLLVM.Function.UnsafeReference

  /// `true` iff the function being compiled is a subscript ramp.
  ///
  /// This property is `if` when `value` represents either the entry point of a subscript or some
  /// plateau covering a projection whose start dominates a `yield` instruction, in which case
  /// `isPlateau` is also `true`.
  internal let isRamp: Bool

  /// `true` iff the function being compiled is a plateau covering the uses of a projection.
  internal var isPlateau: Bool {
    prototype.mapping.output == nil
  }

}

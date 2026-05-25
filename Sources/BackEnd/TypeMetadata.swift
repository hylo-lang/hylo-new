import SwiftyLLVM

/// Information about the LLVM representation of a type compiled from Hylo.
internal struct TypeMetadata {

  /// A handle to the LLVM instance representing the type.
  internal let llvm: SwiftyLLVM.AnyType.UnsafeReference

  /// Information about the size, alignment, and fields of the type.
  internal let layout: ConcreteLayout

}

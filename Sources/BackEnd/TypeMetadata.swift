import SwiftyLLVM

/// Information about the LLVM representation of a type compiled from Hylo.
internal struct TypeMetadata {

  /// A handle to the LLVM instance representing the type.
  internal let llvm: LLVMType

  /// Information about the size, alignment, and fields of the type.
  internal let layout: ConcreteLayout

  /// Creates an instance with the given properties.
  internal init<T: SwiftyLLVM.IRType>(llvm: T.UnsafeReference, layout: ConcreteLayout) {
    self.llvm = llvm.asAnyType
    self.layout = layout
  }

}

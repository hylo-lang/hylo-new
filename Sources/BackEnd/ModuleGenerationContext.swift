import FrontEnd
import SwiftyLLVM

/// A Hylo module.
internal typealias HyloModule = FrontEnd.Module

/// A SwiftyLLVM module.
internal typealias LLVMModule = SwiftyLLVM.Module

/// The state of the compilation of a LLVM IR module from a Hylo IR module.
internal struct ModuleGenerationContext: ~Copyable {

  /// The Hylo module being compiled.
  internal let hylo: HyloModule.ID

  /// The LLVM module being built.
  internal var llvm: LLVMModule

  /// A map from a type's mangled name to its metadata.
  internal var typeMetadata: [String: TypeMetadata]

  /// The set of Hylo functions that have been compiled.
  internal var compiled: Set<FrontEnd.IRFunction.ID>

  /// A zero-sized type.
  internal let empty: SwiftyLLVM.StructType.UnsafeReference

  /// Creates the initial state of a compilation of `m`.
  internal init(compiling hylo: HyloModule.ID, into llvm: consuming LLVMModule) {
    self.hylo = hylo
    self.llvm = llvm
    self.typeMetadata = [:]
    self.compiled = []
    self.empty = self.llvm.structType([])
  }

  /// Returns the resources held by this instance.
  internal consuming func release() -> LLVMModule {
    llvm
  }

}

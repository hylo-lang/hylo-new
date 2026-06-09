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

  /// A map from a function's name to its metadata.
  internal var functionMetadata: [IRFunction.Name: FunctionMetadata]

  /// The set of Hylo functions that have been compiled.
  internal var compiled: Set<FrontEnd.IRFunction.ID>

  /// A zero-sized type.
  internal let empty: SwiftyLLVM.StructType.UnsafeReference

  /// The type of a subscript slide.
  ///
  /// A slide is a function that accepts a pointer to values captured from the corresponding ramp.
  internal let slide: SwiftyLLVM.FunctionType.UnsafeReference

  /// The type of a plateau encapsulating the uses of a subscript application.
  ///
  /// A plateau is a function encapsulating the uses of a value projected by a subscript. It is
  /// called by that subscript's ramp and is expected to call the corresponding slide exactly once
  /// before returning, on every paths.
  ///
  /// A plateau accepts four pointers, referring to:
  /// - the value projected by a subscript;
  /// - the environment of the code extracted out of the caller to form the plateau;
  /// - the function implementing the subscript's slide; and
  /// - the environment of the subscript's slide.
  ///
  /// The return value of a plateau is a 32-bit integer specifying how to transfer control flow
  /// once the plateau (and subsequently the subscript having called it) returns.
  internal let plateau: SwiftyLLVM.FunctionType.UnsafeReference

  internal let nestedProject: SwiftyLLVM.StructType.UnsafeReference

  /// Creates the initial state of a compilation of `m`.
  internal init(compiling hylo: HyloModule.ID, into llvm: consuming LLVMModule) {
    self.hylo = hylo
    self.llvm = llvm
    self.typeMetadata = [:]
    self.functionMetadata = [:]
    self.compiled = []

    let fun = self.llvm.functionPointer.asAnyType
    let ptr = self.llvm.ptr.asAnyType
    let i32 = self.llvm.i32.asAnyType

    self.empty = self.llvm.structType([])
    self.slide = self.llvm.functionType(from: [ptr])
    self.plateau = self.llvm.functionType(from: [ptr, ptr, fun, ptr], to: i32)
    self.nestedProject = self.llvm.structType([ptr, fun, fun])
  }

  /// Returns the resources held by this instance.
  internal consuming func release() -> LLVMModule {
    llvm
  }

}

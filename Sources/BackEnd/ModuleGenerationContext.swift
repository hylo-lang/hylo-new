import FrontEnd
import SwiftyLLVM

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

  /// A map from a string constant to its representation in the module.
  internal var strings: [String: LLVMValue]

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

  /// The type of a pair representing a plateau callback.
  ///
  /// A plateau callback is composed of a pointer to a plateau function and a pointer to that
  /// function's' environment. It corresponds to the values of the two last parameters passed to
  /// a subscript ramp.
  internal let plateauCallback: SwiftyLLVM.StructType.UnsafeReference

  /// The data structure representing ongoing projections captured by a slide or plateau.
  ///
  /// When the result of a subscript has to be used in a plateau, a triple is formed with the
  /// addresses of the projected value, the slide, and its environment.
  internal let nestedProject: SwiftyLLVM.StructType.UnsafeReference

  /// The header of the structure representing information stored in all type witnesses.
  ///
  /// A type witness is a 4-tuple optionally followed by a buffer of pointers, containing:
  /// - A string describing the type being witnessed;
  /// - The size of the type, as a 32-bit unsigned integer;
  /// - The alignment of the type, as a 16-bit unsigned ingeter;
  /// - The number of type parameters or type arguments, encoded using a 16-bit signed integer.
  ///
  /// Let `n` be the value of the 4-th component. If `n` is non-negative, then the witness is for a
  /// proper type, `n` is the arity of the constructor that formed this type, and the tail buffer
  /// contains a pointer to the witnesses the type arguments. Otherwise, the witness is for a type
  /// constructor of arity `-n` and the tail buffer contains a pointer to a function implementing
  /// that constructor.
  internal let typeWitnessHeader: [LLVMType]

  /// Creates the initial state of a compilation of `m`.
  internal init(compiling hylo: HyloModule.ID, into llvm: consuming LLVMModule) {
    self.hylo = hylo
    self.llvm = llvm
    self.typeMetadata = [:]
    self.functionMetadata = [:]
    self.strings = [:]
    self.compiled = []

    let fun = self.llvm.functionPointer.t
    let ptr = self.llvm.ptr.t
    let iptr = self.llvm.iptr.t
    let i32 = self.llvm.i32.t
    let i16 = self.llvm.i16.t

    self.empty = self.llvm.structType([])
    self.slide = self.llvm.functionType(from: [ptr])
    self.plateau = self.llvm.functionType(from: [ptr, ptr, fun, ptr], to: i32)
    self.nestedProject = self.llvm.structType([ptr, fun, ptr])
    self.plateauCallback = self.llvm.structType([fun, ptr])
    self.typeWitnessHeader = [iptr, i32, i16, i16]
  }

  /// Returns the resources held by this instance.
  internal consuming func release() -> LLVMModule {
    llvm
  }

  /// Returns an unsigned integer type large enough to represent `n`.
  internal func integerTypeToRepresent(_ n: Int) -> SwiftyLLVM.IntegerType.UnsafeReference {
    switch n {
    case _ where n <= 0xff:
      return llvm.i8
    case _ where n <= 0xffff:
      return llvm.i16
    case _ where n <= 0xffffffff:
      return llvm.i32
    default:
      return llvm.i64
    }
  }

}

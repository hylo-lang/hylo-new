import SwiftyLLVM

/// Information about the LLVM representation of a function compiled from Hylo.
internal struct FunctionMetadata {

  /// How arguments to a parameter in Hylo IR are passed in the corresponding LLVM IR.
  internal enum PassingConvention {

    /// The parameter does not appear in the signature of the LLVM function.
    case erased

    /// The argument is passed by value in the LLVM function.
    ///
    /// Let `p` be a parameter in Hylo IR, the payload is either the index of the corresponding
    /// parameter in the LLVM function or `-1` if `p` is an output parameter returned by value.
    case byValue(Int)

    /// The argument is passed by reference in the LLVM function.
    ///
    /// The payload is the index of the corresponding parameter in the LLVM function.
    case byReference(Int)

  }

  /// The description of the way a parameter in Hylo IR is being represented in LLVM IR.
  internal struct Parameter {

    /// The type of the parameter.
    internal let type: TypeMetadata

    /// The way in which arguments to the parameter are passed.
    internal let convention: PassingConvention

  }

  /// A handle to the LLVM instance representing the compiled function.
  internal let llvm: SwiftyLLVM.Function.UnsafeReference

  /// A table mapping each term parameter of the Hylo function to its passing convention.
  internal let inputs: [Parameter]

  /// The passing convention of the return value.
  internal let output: Parameter

}

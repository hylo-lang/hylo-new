import SwiftyLLVM

/// The signature of a LLVM IR function compiled form a Hylo IR function.
internal struct Prototype {

  /// How arguments to a parameter in Hylo IR are passed in the corresponding LLVM IR.
  internal enum PassingConvention: Equatable {

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
    internal let convention: Prototype.PassingConvention

  }

  /// How the parameters and return value of a function in Hylo IR are mapped to the parameters and
  /// return value of the corresponding function in LLVM IR.
  internal struct Mapping {

    /// A table mapping each term parameter of the Hylo function to its passing convention.
    ///
    /// This property describes how each parameter of a Hylo IR function are represented (or not)
    /// in the corresponding LLVM function. It contains exactly as many elements as the number of
    /// input parameters in the Hylo IR function. The compiled LLVM function, however, may have a
    /// different number of parameters. Some may have been erased or added to implement Hylo's ABI.
    internal let inputs: [Prototype.Parameter]

    /// The passing convention of the return value iff the compiled function is not a plateau;
    /// otherwise, `nil`.
    internal let output: Prototype.Parameter?

  }

  /// The type of the LLVM function.
  internal let signature: SwiftyLLVM.FunctionType.UnsafeReference

  /// How the parameters of the Hylo IR function are represented in the LLVM function.
  internal let mapping: Mapping

}

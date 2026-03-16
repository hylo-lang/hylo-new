import SwiftyLLVM

extension SwiftyLLVM.Module {

  /// Returns the LLVM declaration of `malloc`.
  private mutating func mallocPrototype() -> SwiftyLLVM.Function.UnsafeReference {
    if let f = function(named: "malloc") {
      return f
    }

    let f = declareFunction(
      "malloc",
      functionType(from: (layout.pointerSizedIntegerType), to: ptr))
    // todo use size_t instead of intptr_t. They are not the same size on all platforms.

    addParameterAttribute(named: .noundef, to: f.unsafe[].parameters[0])
    addReturnAttribute(named: .noalias, to: f)

    return f
  }

  /// Returns the declaration of `free`.
  private mutating func freePrototype() -> SwiftyLLVM.Function.UnsafeReference {
    if let f = function(named: "free") {
      return f
    }

    let f = declareFunction(
      "free",
      functionType(from: (ptr), to: void))
    addParameterAttribute(named: .noundef, to: f.unsafe[].parameters[0])

    return f
  }
}
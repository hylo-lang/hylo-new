import FrontEnd
import SwiftyLLVM

/// The state of the compilation of a LLVM IR function from a Hylo IR function.
internal struct FunctionGenerationContext: ~Copyable {

  /// The state part of `self` related to the whole module being compiled.
  internal var module: ModuleGenerationContext

  /// The Hylo function being compiled.
  internal let ir: FrontEnd.IRFunction

  /// The dominance relation of the function being compiled.
  internal let dominance: DominatorTree

  /// The LLVM function being built, along with information about its configuration.
  internal let result: FunctionMetadata

  /// A map from Hylo IR basic block to its LLVM counterpart.
  internal var block: [FrontEnd.IRBlock.ID: SwiftyLLVM.BasicBlock.UnsafeReference]

  /// A map from Hylo IR register to its LLVM counterpart, unless it has been erased.
  internal var value: [FrontEnd.IRValue: LLVMValue]

  /// The set of basic blocks that have been factored out into a plateau.
  internal var factoredOut: IRBlockSet

  /// Where new LLVM IR instruction are inserted.
  internal var insertionPoint: SwiftyLLVM.InsertionPoint?

  /// Creates an instance with the given properties.
  internal init(
    compiling ir: IRFunction, within dominance: DominatorTree, into result: FunctionMetadata,
    in context: consuming ModuleGenerationContext
  ) {
    self.module = context
    self.ir = ir
    self.dominance = dominance
    self.result = result
    self.block = [:]
    self.value = [:]
    self.factoredOut = []
    self.insertionPoint = nil
  }

  /// The LLVM function being built.
  internal var llvm: SwiftyLLVM.Function.UnsafeReference {
    result.value
  }

  /// Returns the resources held by this instance.
  internal consuming func release() -> ModuleGenerationContext {
    module
  }

  /// Returns the LLVM basic block corresponding to `b`, creating it if necessary.
  internal mutating func demandBasicBlock(
    _ b: IRBlock.ID
  ) -> SwiftyLLVM.BasicBlock.UnsafeReference {
    if let r = block[b] {
      return r
    } else {
      let v = module.llvm.appendBlock(to: llvm)
      block[b] = v
      return v
    }
  }

  /// Returns the value of the plateau callback that has been captured and passed to the function
  /// being compiled, which is the plateau of a projection started in a ramp.
  internal mutating func insertExtractCapturedPlateau() -> (LLVMValue, LLVMValue) {
    assert(result.isRamp && result.isPlateau)

    let t = module.plateauCallback
    let u = module.llvm.structType([t.t])
    let x = module.llvm.insertGetStructElementPointer(
      of: llvm.unsafe[].parameters[1], typed: u, index: 0, at: insertionPoint!)
    let p = module.llvm.insertLoad(t, from: x, at: insertionPoint!)

    let f = module.llvm.insertExtractValue(from: p, at: 0, at: insertionPoint!)
    let e = module.llvm.insertExtractValue(from: p, at: 1, at: insertionPoint!)
    return (f.v, e.v)
  }

  /// Returns the value of the plateau callback of the ramp being compiled.
  ///
  /// If the function being compiled is a plateau, then the callback is read from its second
  /// parameter, which is the environment of the code covered by the plateau. Otherwise, the
  /// callback is defined by the last two parameters of the function.
  internal mutating func insertExtractPlateau() -> (LLVMValue, LLVMValue) {
    if result.isPlateau {
      return insertExtractCapturedPlateau()
    } else {
      assert(result.isRamp)
      let f = llvm.unsafe[].parameters[toLast: 1]
      let e = llvm.unsafe[].parameters[toLast: 0]
      return(f.v, e.v)
    }
  }

}

import FrontEnd
import SwiftyLLVM

/// The state of the compilation of a LLVM IR function from a Hylo IR function.
internal struct FunctionGenerationContext: ~Copyable {

  /// The state part of `self` related to the whole module being compiled.
  internal var module: ModuleGenerationContext

  /// The Hylo function being compiled.
  internal let ir: FrontEnd.IRFunction

  /// The dominance relation of the function being compiled.
  internal let dominance: FrontEnd.DominatorTree

  /// The LLVM function being built, along with information about its configuration.
  internal let result: FunctionMetadata

  /// A map from Hylo IR basic block to its LLVM counterpart.
  internal var block: [FrontEnd.IRBlock.ID: SwiftyLLVM.BasicBlock.UnsafeReference]

  /// A map from Hylo IR register to its LLVM counterpart, unless it has been erased.
  internal var value: [FrontEnd.IRValue: SwiftyLLVM.AnyValue.UnsafeReference]

  /// The set of basic blocks that have been factored out into a plateau.
  internal var factoredOut: IRBlockSet

  /// Where new LLVM IR instruction are inserted.
  internal var insertionPoint: SwiftyLLVM.InsertionPoint?

  /// Creates an instance with the given properties.
  internal init(
    compiling ir: IRFunction, within cfg: ControlFlowGraph, into result: FunctionMetadata,
    in context: consuming ModuleGenerationContext
  ) {
    self.module = context
    self.ir = ir
    self.dominance = DominatorTree(function: ir, controlFlow: cfg)
    self.result = result
    self.block = [:]
    self.value = [:]
    self.factoredOut = []
    self.insertionPoint = nil
  }

  /// The LLVM function being built.
  internal var llvm: SwiftyLLVM.Function.UnsafeReference {
    result.llvm
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

}

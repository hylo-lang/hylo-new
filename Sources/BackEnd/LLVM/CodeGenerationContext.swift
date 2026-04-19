import FrontEnd
import SwiftyLLVM
import Utilities

extension Program {

  /// Compiles the IR of `m` for target `t`.
  ///
  /// - Requires: `m` has been lowered and all required passes have been run.
  public func compileToLLVM(_ m: FrontEnd.Module.ID, target t: consuming TargetMachine) throws -> SwiftyLLVM.Module {
    var llvm = try SwiftyLLVM.Module("MainModule", targetMachine: t)

    // FIXME: Emitting trivial main function for now. Replace with actual code generation.

    // fun main() -> Int32 { 0 }
    let mainType = llvm.functionType(from: (), to: llvm.i32)
    let main = llvm.declareFunction("main", mainType)

    let entry = llvm.appendBlock(to: main)
    llvm.insertReturn(llvm.i32.unsafe[].zero, at: llvm.endOf(entry))

    return llvm
  }

}
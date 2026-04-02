import FrontEnd
import SwiftyLLVM
import Utilities

extension SwiftyLLVM.OverflowBehavior {

  /// An instance equivalent to `x`
  fileprivate init(_ x: FrontEnd.OverflowBehavior) {
    switch x {
    case .ignore: self = .ignore
    case .nsw: self = .nsw
    case .nuw: self = .nuw
    }
  }

}
extension SwiftyLLVM.IntegerPredicate {

  /// An instance equivalent to `x`
  fileprivate init(_ x: FrontEnd.IntegerPredicate) {
    switch x {
    case .eq: self = .eq
    case .slt: self = .slt
    case .sle: self = .sle
    case .sgt: self = .sgt
    case .sge: self = .sge
    case .ugt: self = .ugt
    case .uge: self = .uge
    case .ne: self = .ne
    case .ult: self = .ult
    case .ule: self = .ule
    }
  }

}

extension SwiftyLLVM.FloatingPointPredicate {

  /// An instance equivalent to `x`
  fileprivate init(_ x: FrontEnd.FloatingPointPredicate) {
    switch x {
    case .alwaysFalse: self = .alwaysFalse
    case .alwaysTrue: self = .alwaysTrue
    case .oeq: self = .oeq
    case .one: self = .one
    case .ogt: self = .ogt
    case .oge: self = .oge
    case .olt: self = .olt
    case .ole: self = .ole
    case .ord: self = .ord
    case .ueq: self = .ueq
    case .une: self = .une
    case .ugt: self = .ugt
    case .uge: self = .uge
    case .ult: self = .ult
    case .ule: self = .ule
    case .uno: self = .uno
    }
  }

}

public struct CodeGenerationContext: ~Copyable {
  private let program: Program
  public var llvm: SwiftyLLVM.Module
  private let moduleID: FrontEnd.Module.ID

  public let functions: [FrontEnd.IRFunction]
  public var isFunctionTranspiled: [Bool]

  private init(
    transpiling module: FrontEnd.Module.ID, in program: Program,
    compilingFor targetMachine: consuming SwiftyLLVM.TargetMachine
  ) throws {
    self.llvm = try SwiftyLLVM.Module(
      program.modules.elements[module].key, targetMachine: targetMachine)
    self.program = program
    self.moduleID = module
    // FIXME: avoid copying the whole array a second time. FrontEnd could expose an array instead of an opaque collection.
    self.functions = program.modules.elements[module].value.functions.map { $0 }
    self.isFunctionTranspiled = Array(repeating: false, count: functions.count)
  }

  /// Incorporates all IR entities from an IR module to an LLVM module.
  public static func transpiling(
    _ module: FrontEnd.Module.ID, in program: Program,
    compilingFor targetMachine: consuming SwiftyLLVM.TargetMachine
  ) throws -> Self {
    var context = try Self(transpiling: module, in: program, compilingFor: targetMachine)
    for f in context.functions.indices {
      try context.incorporate(functionWithIndex: f)
    }
    return context
  }

  /// Extracts the LLVM module while consuming the code generation context.
  public consuming func extractModule() -> SwiftyLLVM.Module {
    consume llvm
  }

  /// The IR of the module being lowered.
  var sourceModule: FrontEnd.Module {
    get { program.modules.elements[moduleID].value }
  }

  mutating func incorporate(functionWithIndex i: Int) throws {
    /// Don't re-transpile functions. TODO see if this is actually necessary.
    if isFunctionTranspiled[i] { return }
    isFunctionTranspiled[i] = true

    let f = functions[i]

    /// Don't transpile generic functions.
    if f.isGeneric { return }

    // Don't transpile projections.
    guard let _ = f.returnRegister else {
      var p = TreePrinter(program: program)
      print("WARNING: function \(p.show(f.name)) has no return register, probably it's a subscript that we didn't lower yet.")
      return
    }

    let transpiledFunction = declareFunction(transpiledFrom: f)

    transpile(contentsOf: f, into: transpiledFunction)

    if program.isModuleEntry(f) {
      defineMain(calling: f)
    }
  }

  /// Inserts or retrieves the transpiled declaration of an IR function `f`.
  mutating func declareFunction(transpiledFrom f: IRFunction) -> SwiftyLLVM.Function.UnsafeReference
  {
    // Parameters and return values are passed by reference.
    let parameters = Array(repeating: llvm.ptr.erased, count: f.termParameters.count)
    let name = program.llvmName(of: f)
    let transpiledFunction = llvm.declareFunction(name, llvm.functionType(from: parameters))

    configureFunctionAttributes(function: transpiledFunction, transpiledFrom: f, in: sourceModule)
    configureParameterAttributes(
      parameters: transpiledFunction.unsafe[].parameters, transpiledFrom: f,
      in: sourceModule)

    return transpiledFunction
  }

  /// Defines a "main" function calling the function `f`, which represents the entry point of the
  /// entry module `m` of the program `ir`.
  ///
  /// This method creates a LLVM entry point calling `f`, which is the lowered form of a public
  /// function named "main", taking no parameter and returning either `Void` or `Int32`. `f` will
  /// be linked privately in `m`.
  private mutating func defineMain(calling f: IRFunction) {
    let main = llvm.declareFunction("main", llvm.functionType(from: (), to: llvm.i32))

    let b = llvm.appendBlock(to: main)
    let p = llvm.endOf(b)

    let transpilation = llvm.function(named: program.llvmName(of: f))!
    llvm.setLinkage(.private, for: transpilation)

    let int32 = program.standardLibraryType(.int32)

    if let r = f.returnRegister,
      let rt = f.result(of: r),
      rt.type == int32
    {
      // Calling as `fun main() -> Int32`
      let t = StructType.UnsafeReference(program.llvmType(from: int32, in: &llvm))!
      let s = llvm.insertAlloca(t, at: p)
      _ = llvm.insertCall(transpilation, on: (s), at: p)

      let statusPointer = llvm.insertGetStructElementPointer(of: s, typed: t, index: 0, at: p)
      let status = llvm.insertLoad(llvm.i32, from: statusPointer, at: p)
      llvm.insertReturn(status, at: p)
    } else {
      // Calling as `fun main() -> Void`
      let t = program.llvmType(from: AnyTypeIdentity.void, in: &llvm)
      let s = llvm.insertAlloca(t, at: p)
      _ = llvm.insertCall(transpilation, on: (s), at: p)
      llvm.insertReturn(llvm.i32.unsafe[].zero, at: p)
    }
  }

  /// Adds the function attributes to `llvmFunction` implied by its IR form `f`.
  private mutating func configureFunctionAttributes(
    function llvmFunction: SwiftyLLVM.Function.UnsafeReference, transpiledFrom f: IRFunction,
    in m: FrontEnd.Module
  ) {
    // TODO add linkage attributes in IR
    // if f.linkage == .module {
    //   setLinkage(.private, for: llvmFunction)
    // }

    guard
      let (type, _) = f.result(
        of: f.returnRegister
          ?? fatalError("function expected to be a regular function, not a subscript"))
    else {
      var p = TreePrinter(program: program)
      fatalError("Why did we not get a result type of \(f.show(using: &p))?")
    }

    _ = type
    // FIXME cannot call mutating never() method
    // if type != program.types.never() {
    //   addFunctionAttribute(functionAttribute(.noreturn), to: llvmFunction)
    // }
  }

  /// Adds the attributes to each parameter in `llvmParameters` implied by their corresponding IR
  /// form in `m[f].termParameters`.
  private mutating func configureParameterAttributes(
    parameters llvmParameters: SwiftyLLVM.Function.Parameters,
    transpiledFrom f: IRFunction, in m: FrontEnd.Module
  ) {
    assert(llvmParameters.count == f.termParameters.count)
    for (p, l) in llvmParameters.enumerated() {
      configureParameterAttributes(parameter: l, access: f.termParameters[p].access, in: m)
    }
  }

  /// Adds the attributes to `llvmParameter` implied by `access`.
  private mutating func configureParameterAttributes(
    parameter llvmParameter: SwiftyLLVM.Parameter.UnsafeReference,
    access accessEffect: FrontEnd.AccessEffect, in m: FrontEnd.Module
  ) {
    llvm.addParameterAttribute(named: .noalias, to: llvmParameter)
    llvm.addParameterAttribute(named: .nofree, to: llvmParameter)
    llvm.addParameterAttribute(named: .nocapture, to: llvmParameter)

    if accessEffect == .let {
      llvm.addParameterAttribute(named: .readonly, to: llvmParameter)
    }
  }

  /// Inserts into `transpilation `the transpiled contents of `f`, which is a function or subscript
  /// of `m` in `ir`.
  ///
  /// - Requires: `transpilation` contains no instruction.
  private mutating func transpile(
    contentsOf f: IRFunction,
    into transpiledFunction: SwiftyLLVM.Function.UnsafeReference
  ) {
    assert(transpiledFunction.unsafe[].basicBlocks.isEmpty)

    /// The function's entry.
    guard let entry = f.entry else { return }

    /// Where new LLVM IR instruction are inserted.
    var insertionPoint: SwiftyLLVM.InsertionPoint!

    /// A map from Hylo IR basic block to its LLVM counterpart.
    var block: [IRBlock.ID: SwiftyLLVM.BasicBlock.UnsafeReference] = [:]

    /// A map from Hylo IR register to its LLVM counterpart.
    var register: [FrontEnd.IRValue: AnyValue.UnsafeReference] = [:]

    /// The prologue of the transpiled function, which contains its stack allocations.
    let prologue = llvm.appendBlock(named: "prologue", to: transpiledFunction)

    /// Record the registers of LLVM function parameters to the register table.
    for i in f.termParameters.indices {
      let o = IRValue.parameter(i)
      register[o] = transpiledFunction.unsafe[].parameters[i].erased
    }

    // Append all blocks of the function.
    for b in f.blocks.addresses {
      block[b] = llvm.appendBlock(named: "b\(b)", to: transpiledFunction)
    }

    for b in f.blocks.addresses {
      insertionPoint = llvm.endOf(block[b]!)
      for i in f.instructions(in: b) {
        insert(i)
      }
    }

    llvm.insertBr(to: block[entry]!, at: llvm.endOf(prologue))

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(_ i: AnyInstructionIdentity) {
      switch f.tag(of: i) {
      case IRAccess.self:
        insert(access: i)
      case IRAccess.End.self:
        return  // No LLVM semantics.
      case IRAlloca.self:
        insert(alloca: i)
      case IRApply.self:
        insert(apply: i)
      case IRApplyBuiltin.self:
        insert(applyBuiltin: i)
      case IRAssumeState.self:
        return  // No LLVM semantics.
      case IRBranch.self:
        insert(branch: i)
      case IRConditionalBranch.self:
        insert(conditionalBranch: i)
      case IRLoad.self:
        insert(load: i)
      case IRMemoryCopy.self:
        insert(memoryCopy: i)
      case IRMove.self:
        fatalError("Unexpected IRMove instruction.")
      case IRProject.self:
        fatalError("Unexpected IRProject instruction.")
      case IRProject.End.self:
        fatalError("Unexpected IRProject.End instruction.")
      case IRProperty.self:
        unimplemented("LLVM lowering for IRProperty")
      case IRReturn.self:
        insert(return: i)
      case IRStore.self:
        insert(store: i)
      case IRSubfield.self:
        insert(subfield: i)
      case IRTypeApply.self:
        unimplemented("LLVM lowering for IRTypeApply")  // Does this even have LLVM semantics?
      case IRUnreachable.self:
        insert(unreachable: i)
      case IRWitnessTable.self:
        unimplemented("LLVM lowering for IRWitnessTable")
      case IRYield.self:
        fatalError("Unexpected IRYield instruction.")
      default:
        unimplemented()
      }
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(alloca i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRAlloca
      let t = program.llvmType(from: s.storageType, in: &llvm)
      if llvm.layout.storageSize(of: t) == 0 {
        register[.register(i)] = llvm.ptr.unsafe[].null.erased
      } else {
        register[.register(i)] = llvm.insertAlloca(t, atEntryOf: transpiledFunction).erased
      }
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(access i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRAccess
      register[.register(i)] = llvmOperand(s.source)
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(branch i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRBranch
      llvm.insertBr(to: block[s.target]!, at: insertionPoint)
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(apply i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRApply
      var arguments: [AnyValue.UnsafeReference] = []

      // Callee is evaluated first; environment is passed before explicit arguments.
      let callee = unpackCallee(of: s.callee)
      arguments.append(contentsOf: callee.environment)

      // Arguments and return value are passed by reference.
      arguments.append(contentsOf: s.arguments.map(llvmOperand(_:)))
      arguments.append(llvmOperand(s.result))
      _ = llvm.insertCall(callee.function, typed: callee.type, on: arguments, at: insertionPoint)
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(conditionalBranch i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRConditionalBranch
      let c = llvmOperand(s.condition)
      llvm.insertCondBr(
        if: c, then: block[s.onSuccess]!, else: block[s.onFailure]!,
        at: insertionPoint)
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(subfield i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRSubfield

      let base = llvmOperand(s.base)
      let baseType = program.llvmType(from: f.result(of: s.base)!.type, in: &llvm)
      let indices =
        [llvm.i32.unsafe[].constant(0).erased]
        + s.path.map { sf in llvm.i32.unsafe[].constant(UInt64(sf)).erased }
      let v = llvm.insertGetElementPointerInBounds(
        of: base, typed: baseType, indices: indices, at: insertionPoint)
      register[.register(i)] = v.erased
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(applyBuiltin i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRApplyBuiltin
      switch s.callee {
      case .add(let p, _):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] = llvm.insertAdd(overflow: .init(p), l, r, at: insertionPoint).erased

      case .sub(let p, _):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] = llvm.insertSub(overflow: .init(p), l, r, at: insertionPoint).erased

      case .mul(let p, _):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] = llvm.insertMul(overflow: .init(p), l, r, at: insertionPoint).erased

      // case .shl:
      //   let l = llvmOperand(s.operands[0])
      //   let r = llvmOperand(s.operands[1])
      //   register[.register(i)] = llvm.insertShl(l, r, at: insertionPoint).erased

      // case .lshr:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertLShr(l, r, at: insertionPoint).erased

      // case .ashr:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertAShr(l, r, at: insertionPoint).erased

      // case .sdiv(let e, _):
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertSignedDiv(exact: e, l, r, at: insertionPoint).erased

      // case .udiv(let e, _):
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertUnsignedDiv(exact: e, l, r, at: insertionPoint).erased

      // case .srem:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertSignedRem(l, r, at: insertionPoint).erased

      // case .urem:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertUnsignedRem(l, r, at: insertionPoint).erased

      case .signedAdditionWithOverflow(let t):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        let x = llvm.intrinsic(
          named: IntrinsicFunction.llvm.sadd.with.overflow,
          for: [program.llvmType(from: t, in: &llvm)])!
        register[.register(i)] = llvm.insertCall(x, on: [l, r], at: insertionPoint).erased

      case .unsignedAdditionWithOverflow(let t):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        let x = llvm.intrinsic(
          named: IntrinsicFunction.llvm.uadd.with.overflow,
          for: (program.llvmType(from: t, in: &llvm)))!
        register[.register(i)] = llvm.insertCall(x, on: (l, r), at: insertionPoint).erased

      case .signedSubtractionWithOverflow(let t):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        let x = llvm.intrinsic(
          named: IntrinsicFunction.llvm.ssub.with.overflow,
          for: (program.llvmType(from: t, in: &llvm)))!
        register[.register(i)] = llvm.insertCall(x, on: (l, r), at: insertionPoint).erased

      case .unsignedSubtractionWithOverflow(let t):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        let x = llvm.intrinsic(
          named: IntrinsicFunction.llvm.usub.with.overflow,
          for: (program.llvmType(from: t, in: &llvm)))!
        register[.register(i)] = llvm.insertCall(x, on: (l, r), at: insertionPoint).erased

      case .signedMultiplicationWithOverflow(let t):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        let x = llvm.intrinsic(
          named: IntrinsicFunction.llvm.smul.with.overflow,
          for: [program.llvmType(from: t, in: &llvm)])!
        register[.register(i)] = llvm.insertCall(x, on: [l, r], at: insertionPoint).erased

      case .unsignedMultiplicationWithOverflow(let t):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        let x = llvm.intrinsic(
          named: IntrinsicFunction.llvm.umul.with.overflow,
          for: (program.llvmType(from: t, in: &llvm)))!
        register[.register(i)] = llvm.insertCall(x, on: (l, r), at: insertionPoint).erased

      case .icmp(let p, _):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] =
          llvm.insertIntegerComparison(.init(p), l, r, at: insertionPoint).erased

      case .and(_):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] = llvm.insertBitwiseAnd(l, r, at: insertionPoint).erased

      case .or(_):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] = llvm.insertBitwiseOr(l, r, at: insertionPoint).erased

      case .xor(_):
        let l = llvmOperand(s.operands[0])
        let r = llvmOperand(s.operands[1])
        register[.register(i)] = llvm.insertBitwiseXor(l, r, at: insertionPoint).erased

      // case .trunc(_, let t):
      //   let target = program.llvmType(from: t, in: &llvm)
      //   let source = llvmOperand(s.operands[0])
      //   register[.register(i)] = llvm.insertTrunc(source, to: target, at: insertionPoint).erased

      // case .zext(_, let t):
      //   let target = program.llvmType(from: t, in: &llvm)
      //   let source = llvm(s.operands[0])
      //   register[.register(i)] = insertZeroExtend(source, to: target, at: insertionPoint).erased

      // case .sext(_, let t):
      //   let target = program.llvmType(from: t, in: &llvm)
      //   let source = llvm(s.operands[0])
      //   register[.register(i)] = insertSignExtend(source, to: target, at: insertionPoint).erased

      // case .inttoptr(_):
      //   let source = llvm(s.operands[0])
      //   register[.register(i)] = insertIntToPtr(source, at: insertionPoint).erased

      // case .ptrtoint(let t):
      //   let target = program.llvmType(from: t, in: &llvm)
      //   let source = llvm(s.operands[0])
      //   register[.register(i)] = insertPtrToInt(source, to: target, at: insertionPoint).erased

      // case .fadd:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertFAdd(l, r, at: insertionPoint).erased

      // case .fsub:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertFSub(l, r, at: insertionPoint).erased

      // case .fmul:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertFMul(l, r, at: insertionPoint).erased

      // case .fdiv:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertFDiv(l, r, at: insertionPoint).erased

      // case .frem:
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] = insertFRem(l, r, at: insertionPoint).erased

      // case .fcmp(_, let p, _):
      //   let l = llvm(s.operands[0])
      //   let r = llvm(s.operands[1])
      //   register[.register(i)] =
      //     insertFloatingPointComparison(.init(p), l, r, at: insertionPoint).erased

      // case .fptrunc(_, let t):
      //   let target = program.llvmType(from: t, in: &llvm)
      //   let source = llvm(s.operands[0])
      //   register[.register(i)] = insertFPTrunc(source, to: target, at: insertionPoint).erased

      // case .ctpop(let t):
      //   let source = llvm(s.operands[0])
      //   let x = intrinsic(
      //     named: IntrinsicFunction.llvm.ctpop,
      //     for: (program.llvmType(from: t, in: &llvm)))!
      //   register[.register(i)] = insertCall(x, on: (source), at: insertionPoint).erased

      // case .ctlz(let t):
      //   let source = llvm(s.operands[0])
      //   let x = intrinsic(
      //     named: IntrinsicFunction.llvm.ctlz,
      //     for: (program.llvmType(from: t, in: &llvm)))!

      //   register[.register(i)] =
      //     insertCall(x, on: (source, i1.unsafe[].zero), at: insertionPoint).erased

      // case .cttz(let t):
      //   let source = llvm(s.operands[0])
      //   let x = intrinsic(
      //     named: IntrinsicFunction.llvm.cttz,
      //     for: [program.llvmType(from: t, in: &llvm)])!
      //   register[.register(i)] =
      //     insertCall(x, on: (source, i1.unsafe[].zero), at: insertionPoint).erased

      case .zeroinitializer(let t):
        register[.register(i)] = program.llvmType(from: t, in: &llvm).unsafe[].null.erased

      // case .advancedByBytes:
      //   let base = llvm(s.operands[0])
      //   let byteOffset = llvm(s.operands[1])
      //   register[.register(i)] =
      //     insertGetElementPointerInBounds(
      //       of: base, typed: i8, indices: [byteOffset], at: insertionPoint
      //     ).erased

      // case .atomic_load_relaxed:
      //   let source = llvm(s.operands[0])
      //   let l = insertLoad(ptr, from: source, at: insertionPoint)
      //   setOrdering(.monotonic, for: l)
      //   register[.register(i)] = l.erased

      // case .atomic_load_acquire:
      //   let source = llvm(s.operands[0])
      //   let l = insertLoad(ptr, from: source, at: insertionPoint)
      //   setOrdering(.acquire, for: l)
      //   register[.register(i)] = l.erased

      // case .atomic_load_seqcst:
      //   let source = llvm(s.operands[0])
      //   let l = insertLoad(ptr, from: source, at: insertionPoint)
      //   setOrdering(.sequentiallyConsistent, for: l)
      //   register[.register(i)] = l.erased

      // case .atomic_store_relaxed:
      //   let target = llvm(s.operands[0])
      //   let value = llvm(s.operands[1])
      //   let s = insertStore(value, to: target, at: insertionPoint)
      //   setOrdering(.monotonic, for: s)

      // case .atomic_store_release:
      //   let target = llvm(s.operands[0])
      //   let value = llvm(s.operands[1])
      //   let s = insertStore(value, to: target, at: insertionPoint)
      //   setOrdering(.release, for: s)

      // case .atomic_store_seqcst:
      //   let target = llvm(s.operands[0])
      //   let value = llvm(s.operands[1])
      //   let s = insertStore(value, to: target, at: insertionPoint)
      //   setOrdering(.sequentiallyConsistent, for: s)

      // case .atomic_swap_relaxed:
      //   insert(atomicRMW: .xchg, ordering: .monotonic, for: i)

      // case .atomic_swap_acquire:
      //   insert(atomicRMW: .xchg, ordering: .acquire, for: i)

      // case .atomic_swap_release:
      //   insert(atomicRMW: .xchg, ordering: .release, for: i)

      // case .atomic_swap_acqrel:
      //   insert(atomicRMW: .xchg, ordering: .acquireRelease, for: i)

      // case .atomic_swap_seqcst:
      //   insert(atomicRMW: .xchg, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_add_relaxed:
      //   insert(atomicRMW: .add, ordering: .monotonic, for: i)

      // case .atomic_add_acquire:
      //   insert(atomicRMW: .add, ordering: .acquire, for: i)

      // case .atomic_add_release:
      //   insert(atomicRMW: .add, ordering: .release, for: i)

      // case .atomic_add_acqrel:
      //   insert(atomicRMW: .add, ordering: .acquireRelease, for: i)

      // case .atomic_add_seqcst:
      //   insert(atomicRMW: .add, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_fadd_relaxed:
      //   insert(atomicRMW: .fAdd, ordering: .monotonic, for: i)

      // case .atomic_fadd_acquire:
      //   insert(atomicRMW: .fAdd, ordering: .acquire, for: i)

      // case .atomic_fadd_release:
      //   insert(atomicRMW: .fAdd, ordering: .release, for: i)

      // case .atomic_fadd_acqrel:
      //   insert(atomicRMW: .fAdd, ordering: .acquireRelease, for: i)

      // case .atomic_fadd_seqcst:
      //   insert(atomicRMW: .fAdd, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_sub_relaxed:
      //   insert(atomicRMW: .sub, ordering: .monotonic, for: i)

      // case .atomic_sub_acquire:
      //   insert(atomicRMW: .sub, ordering: .acquire, for: i)

      // case .atomic_sub_release:
      //   insert(atomicRMW: .sub, ordering: .release, for: i)

      // case .atomic_sub_acqrel:
      //   insert(atomicRMW: .sub, ordering: .acquireRelease, for: i)

      // case .atomic_sub_seqcst:
      //   insert(atomicRMW: .sub, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_fsub_relaxed:
      //   insert(atomicRMW: .fSub, ordering: .monotonic, for: i)

      // case .atomic_fsub_acquire:
      //   insert(atomicRMW: .fSub, ordering: .acquire, for: i)

      // case .atomic_fsub_release:
      //   insert(atomicRMW: .fSub, ordering: .release, for: i)

      // case .atomic_fsub_acqrel:
      //   insert(atomicRMW: .fSub, ordering: .acquireRelease, for: i)

      // case .atomic_fsub_seqcst:
      //   insert(atomicRMW: .fSub, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_max_relaxed:
      //   insert(atomicRMW: .max, ordering: .monotonic, for: i)

      // case .atomic_max_acquire:
      //   insert(atomicRMW: .max, ordering: .acquire, for: i)

      // case .atomic_max_release:
      //   insert(atomicRMW: .max, ordering: .release, for: i)

      // case .atomic_max_acqrel:
      //   insert(atomicRMW: .max, ordering: .acquireRelease, for: i)

      // case .atomic_max_seqcst:
      //   insert(atomicRMW: .max, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_umax_relaxed:
      //   insert(atomicRMW: .uMax, ordering: .monotonic, for: i)

      // case .atomic_umax_acquire:
      //   insert(atomicRMW: .uMax, ordering: .acquire, for: i)

      // case .atomic_umax_release:
      //   insert(atomicRMW: .uMax, ordering: .release, for: i)

      // case .atomic_umax_acqrel:
      //   insert(atomicRMW: .uMax, ordering: .acquireRelease, for: i)

      // case .atomic_umax_seqcst:
      //   insert(atomicRMW: .uMax, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_fmax_relaxed:
      //   insert(atomicRMW: .fMax, ordering: .monotonic, for: i)

      // case .atomic_fmax_acquire:
      //   insert(atomicRMW: .fMax, ordering: .acquire, for: i)

      // case .atomic_fmax_release:
      //   insert(atomicRMW: .fMax, ordering: .release, for: i)

      // case .atomic_fmax_acqrel:
      //   insert(atomicRMW: .fMax, ordering: .acquireRelease, for: i)

      // case .atomic_fmax_seqcst:
      //   insert(atomicRMW: .fMax, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_min_relaxed:
      //   insert(atomicRMW: .min, ordering: .monotonic, for: i)

      // case .atomic_min_acquire:
      //   insert(atomicRMW: .min, ordering: .acquire, for: i)

      // case .atomic_min_release:
      //   insert(atomicRMW: .min, ordering: .release, for: i)

      // case .atomic_min_acqrel:
      //   insert(atomicRMW: .min, ordering: .acquireRelease, for: i)

      // case .atomic_min_seqcst:
      //   insert(atomicRMW: .min, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_umin_relaxed:
      //   insert(atomicRMW: .uMin, ordering: .monotonic, for: i)

      // case .atomic_umin_acquire:
      //   insert(atomicRMW: .uMin, ordering: .acquire, for: i)

      // case .atomic_umin_release:
      //   insert(atomicRMW: .uMin, ordering: .release, for: i)

      // case .atomic_umin_acqrel:
      //   insert(atomicRMW: .uMin, ordering: .acquireRelease, for: i)

      // case .atomic_umin_seqcst:
      //   insert(atomicRMW: .uMin, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_fmin_relaxed:
      //   insert(atomicRMW: .fMin, ordering: .monotonic, for: i)

      // case .atomic_fmin_acquire:
      //   insert(atomicRMW: .fMin, ordering: .acquire, for: i)

      // case .atomic_fmin_release:
      //   insert(atomicRMW: .fMin, ordering: .release, for: i)

      // case .atomic_fmin_acqrel:
      //   insert(atomicRMW: .fMin, ordering: .acquireRelease, for: i)

      // case .atomic_fmin_seqcst:
      //   insert(atomicRMW: .fMin, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_and_relaxed:
      //   insert(atomicRMW: .and, ordering: .monotonic, for: i)

      // case .atomic_and_acquire:
      //   insert(atomicRMW: .and, ordering: .acquire, for: i)

      // case .atomic_and_release:
      //   insert(atomicRMW: .and, ordering: .release, for: i)

      // case .atomic_and_acqrel:
      //   insert(atomicRMW: .and, ordering: .acquireRelease, for: i)

      // case .atomic_and_seqcst:
      //   insert(atomicRMW: .and, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_nand_relaxed:
      //   insert(atomicRMW: .nand, ordering: .monotonic, for: i)

      // case .atomic_nand_acquire:
      //   insert(atomicRMW: .nand, ordering: .acquire, for: i)

      // case .atomic_nand_release:
      //   insert(atomicRMW: .nand, ordering: .release, for: i)

      // case .atomic_nand_acqrel:
      //   insert(atomicRMW: .nand, ordering: .acquireRelease, for: i)

      // case .atomic_nand_seqcst:
      //   insert(atomicRMW: .nand, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_or_relaxed:
      //   insert(atomicRMW: .or, ordering: .monotonic, for: i)

      // case .atomic_or_acquire:
      //   insert(atomicRMW: .or, ordering: .acquire, for: i)

      // case .atomic_or_release:
      //   insert(atomicRMW: .or, ordering: .release, for: i)

      // case .atomic_or_acqrel:
      //   insert(atomicRMW: .or, ordering: .acquireRelease, for: i)

      // case .atomic_or_seqcst:
      //   insert(atomicRMW: .or, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_xor_relaxed:
      //   insert(atomicRMW: .xor, ordering: .monotonic, for: i)

      // case .atomic_xor_acquire:
      //   insert(atomicRMW: .xor, ordering: .acquire, for: i)

      // case .atomic_xor_release:
      //   insert(atomicRMW: .xor, ordering: .release, for: i)

      // case .atomic_xor_acqrel:
      //   insert(atomicRMW: .xor, ordering: .acquireRelease, for: i)

      // case .atomic_xor_seqcst:
      //   insert(atomicRMW: .xor, ordering: .sequentiallyConsistent, for: i)

      // case .atomic_cmpxchg_relaxed_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .monotonic, failureOrdering: .monotonic, weak: false, for: i)

      // case .atomic_cmpxchg_relaxed_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .monotonic, failureOrdering: .acquire, weak: false, for: i)

      // case .atomic_cmpxchg_relaxed_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .monotonic, failureOrdering: .sequentiallyConsistent, weak: false, for: i
      //   )

      // case .atomic_cmpxchg_acquire_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquire, failureOrdering: .monotonic, weak: false, for: i)

      // case .atomic_cmpxchg_acquire_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquire, failureOrdering: .acquire, weak: false, for: i)

      // case .atomic_cmpxchg_acquire_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquire, failureOrdering: .sequentiallyConsistent, weak: false, for: i)

      // case .atomic_cmpxchg_release_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .release, failureOrdering: .monotonic, weak: false, for: i)

      // case .atomic_cmpxchg_release_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .release, failureOrdering: .acquire, weak: false, for: i)

      // case .atomic_cmpxchg_release_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .release, failureOrdering: .sequentiallyConsistent, weak: false, for: i)

      // case .atomic_cmpxchg_acqrel_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquireRelease, failureOrdering: .monotonic, weak: false, for: i)

      // case .atomic_cmpxchg_acqrel_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquireRelease, failureOrdering: .acquire, weak: false, for: i)

      // case .atomic_cmpxchg_acqrel_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquireRelease, failureOrdering: .sequentiallyConsistent, weak: false,
      //     for: i)

      // case .atomic_cmpxchg_seqcst_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .sequentiallyConsistent, failureOrdering: .monotonic, weak: false, for: i
      //   )

      // case .atomic_cmpxchg_seqcst_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .sequentiallyConsistent, failureOrdering: .acquire, weak: false, for: i)

      // case .atomic_cmpxchg_seqcst_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .sequentiallyConsistent, failureOrdering: .sequentiallyConsistent,
      //     weak: false, for: i)

      // case .atomic_cmpxchgweak_relaxed_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .monotonic, failureOrdering: .monotonic, weak: true, for: i)

      // case .atomic_cmpxchgweak_relaxed_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .monotonic, failureOrdering: .acquire, weak: true, for: i)

      // case .atomic_cmpxchgweak_relaxed_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .monotonic, failureOrdering: .sequentiallyConsistent, weak: true, for: i)

      // case .atomic_cmpxchgweak_acquire_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquire, failureOrdering: .monotonic, weak: true, for: i)

      // case .atomic_cmpxchgweak_acquire_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquire, failureOrdering: .acquire, weak: true, for: i)

      // case .atomic_cmpxchgweak_acquire_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquire, failureOrdering: .sequentiallyConsistent, weak: true, for: i)

      // case .atomic_cmpxchgweak_release_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .release, failureOrdering: .monotonic, weak: true, for: i)

      // case .atomic_cmpxchgweak_release_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .release, failureOrdering: .acquire, weak: true, for: i)

      // case .atomic_cmpxchgweak_release_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .release, failureOrdering: .sequentiallyConsistent, weak: true, for: i)

      // case .atomic_cmpxchgweak_acqrel_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquireRelease, failureOrdering: .monotonic, weak: true, for: i)

      // case .atomic_cmpxchgweak_acqrel_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquireRelease, failureOrdering: .acquire, weak: true, for: i)

      // case .atomic_cmpxchgweak_acqrel_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .acquireRelease, failureOrdering: .sequentiallyConsistent, weak: true,
      //     for: i)

      // case .atomic_cmpxchgweak_seqcst_relaxed:
      //   insertAtomicCompareExchange(
      //     successOrdering: .sequentiallyConsistent, failureOrdering: .monotonic, weak: true, for: i)

      // case .atomic_cmpxchgweak_seqcst_acquire:
      //   insertAtomicCompareExchange(
      //     successOrdering: .sequentiallyConsistent, failureOrdering: .acquire, weak: true, for: i)

      // case .atomic_cmpxchgweak_seqcst_seqcst:
      //   insertAtomicCompareExchange(
      //     successOrdering: .sequentiallyConsistent, failureOrdering: .sequentiallyConsistent,
      //     weak: true, for: i)

      // case .atomic_fence_acquire:
      //   insertAtomicFence(.acquire, singleThread: false, for: i)

      // case .atomic_fence_release:
      //   insertAtomicFence(.release, singleThread: false, for: i)
      // case .atomic_fence_acqrel:

      //   insertAtomicFence(.acquireRelease, singleThread: false, for: i)
      // case .atomic_fence_seqcst:
      //   insertAtomicFence(.sequentiallyConsistent, singleThread: false, for: i)

      // case .atomic_singlethreadfence_acquire:
      //   insertAtomicFence(.acquire, singleThread: true, for: i)

      // case .atomic_singlethreadfence_release:
      //   insertAtomicFence(.release, singleThread: true, for: i)

      // case .atomic_singlethreadfence_acqrel:
      //   insertAtomicFence(.acquireRelease, singleThread: true, for: i)

      // case .atomic_singlethreadfence_seqcst:
      //   insertAtomicFence(.sequentiallyConsistent, singleThread: true, for: i)

      default:
        unreachable("unexpected LLVM instruction '\(s.callee)'")
      }
    }

    // /// Inserts the transpilation of `i`, which is an `oper`, using `ordering` at `insertionPoint`.
    // func insert(
    //   atomicRMW oper: AtomicRMWBinOp, ordering: AtomicOrdering, for i: AnyInstructionIdentity
    // ) {
    //   let s = f.at(i) as! IR.CallBuiltinFunction
    //   let target = llvmOperand(s.operands[0])
    //   let value = llvmOperand(s.operands[1])
    //   let o = insertAtomicRMW(
    //     target, operation: oper, value: value, ordering: ordering, singleThread: false,
    //     at: insertionPoint)
    //   register[.register(i)] = o.erased
    // }

    // /// Inserts the transpilation of `i` at `insertionPoint`.
    // func insertAtomicCompareExchange(
    //   successOrdering: AtomicOrdering, failureOrdering: AtomicOrdering, weak: Bool,
    //   for i: AnyInstructionIdentity
    // ) {
    //   let s = f.at(i) as! IR.CallBuiltinFunction
    //   let target = llvmOperand(s.operands[0])
    //   let old = llvmOperand(s.operands[1])
    //   let new = llvmOperand(s.operands[2])
    //   let o = insertAtomicCmpXchg(
    //     target,
    //     old: old,
    //     new: new,
    //     successOrdering: successOrdering,
    //     failureOrdering: failureOrdering,
    //     weak: weak,
    //     singleThread: false,
    //     at: insertionPoint)
    //   register[.register(i)] = o.erased
    // }

    // /// Inserts the transpilation of `i` at `insertionPoint`.
    // func insertAtomicFence(
    //   _ ordering: AtomicOrdering, singleThread: Bool, for i: AnyInstructionIdentity
    // ) {
    //   insertFence(ordering, singleThread: singleThread, at: insertionPoint)
    //   register[.register(i)] = ptr.unsafe[].null.erased
    // }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(load i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRLoad
      let t = program.llvmType(from: f.result(of: IRValue.register(i))!.type, in: &llvm)
      let source = llvmOperand(s.source)
      register[.register(i)] = llvm.insertLoad(t, from: source, at: insertionPoint).erased
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(memoryCopy i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRMemoryCopy

      let memcpy = llvm.intrinsic(
        named: IntrinsicFunction.llvm.memcpy, for: (llvm.ptr, llvm.ptr, llvm.i32))!
      let source = llvmOperand(s.source)
      let target = llvmOperand(s.target)

      // let l = ConcreteTypeLayout(
      //   of: f.result(of: s.source)!.type, definedIn: program, forUseIn: &self)
      // let byteCount = llvm.i32.unsafe[].constant(l.size)

      let type = program.llvmType(from: f.result(of: s.source)!.type, in: &llvm)
      let byteCount = llvm.i32.unsafe[].constant(llvm.layout.storageSize(of: type))

      _ = llvm.insertCall(
        memcpy, on: (target, source, byteCount, llvm.i1.unsafe[].zero), at: insertionPoint)
    }

    // /// Inserts the transpilation of `i` at `insertionPoint`.
    // func insert(pointerToPlace i: AnyInstructionIdentity) {
    //   let s = f.at(i) as! IRPointerToPlace
    //   register[.register(i)] = llvmOperand(s.source)
    // }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(return i: AnyInstructionIdentity) {
      llvm.insertReturn(at: insertionPoint)
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(store i: AnyInstructionIdentity) {
      let s = f.at(i) as! IRStore
      let v = llvmOperand(s.value)
      if llvm.layout.storageSize(of: v.unsafe[].type) > 0 {
        llvm.insertStore(v, to: llvmOperand(s.target), at: insertionPoint)
      }
    }

    /// Inserts the transpilation of `i` at `insertionPoint`.
    func insert(unreachable i: AnyInstructionIdentity) {
      llvm.insertUnreachable(at: insertionPoint)
    }

    /// Returns the LLVM IR value corresponding to the Hylo IR operand `o`.
    func llvmOperand(_ o: FrontEnd.IRValue) -> AnyValue.UnsafeReference {
      switch o {
      case .parameter(let i):
        return transpiledFunction.unsafe[].parameters[i].erased
      case .register(let i):
        return register[.register(i)] ?? fatalError("Value not found at register \(i)")  //?? transpiledConstant(VoidConstant(), in: &context)
      case .integer(let v, let t):
        let llvmType = IntegerType.UnsafeReference(
          uncheckedFrom: program.llvmType(from: t, in: &llvm))
        return llvmType.unsafe[].constant(v).erased
      case .function(let name, let t):
        return llvmFunction(named: name, type: t).erased
      case .poison(let t):
        return llvm.poisonValue(of: program.llvmType(from: f.resolved(t)!.type, in: &llvm)).erased
      }
    }

    /// Returns the LLVM function corresponding to `name` and `type`.
    func llvmFunction(named name: IRFunction.Name, type: FrontEnd.AnyTypeIdentity)
      -> SwiftyLLVM.Function.UnsafeReference
    {
      let n = program.llvmName(of: name)

      // todo use mangled name or external name if present
      // todo is there a better way to get the function?
      // Functions from other modules may need to be declared lazily at first use.
      let t =
        program.types.cast(type, to: Arrow.self)
        ?? fatalError("Expected type of a function to be an arrow, but got \(type)")
      return llvm.declareFunction(n, transpiledType(t))
    }

    /// Returns the callee of `s`.
    func unpackCallee(of s: FrontEnd.IRValue) -> ArrowContents {
      if case .function(let name, let t) = s {
        let f = llvmFunction(named: name, type: t)

        return .init(function: f.erased, type: f.unsafe[].valueType, environment: [])
      }

      // `s` is an arrow.
      let hyloType = ConcreteTypeIdentity<Arrow>(uncheckedFrom: f.result(of: s)!.type)
      let llvmType = StructType.UnsafeReference(program.llvmType(from: hyloType, in: &llvm))!
      let lambda = llvmOperand(s)

      // The first element of the representation is the function pointer.
      var f = llvm.insertGetStructElementPointer(
        of: lambda, typed: llvmType, index: 0, at: insertionPoint)
      f = llvm.insertLoad(llvm.ptr, from: f, at: insertionPoint)

      let e = llvm.insertGetStructElementPointer(
        of: lambda, typed: llvmType, index: 1, at: insertionPoint)
      let captures = StructType.UnsafeReference(
        program.llvmType(from: program.types[hyloType].environment, in: &llvm))!

      // Following elements constitute the environment.
      var environment: [AnyValue.UnsafeReference] = []
      for (i, c) in program.types[hyloType].captures(in: program).enumerated() {
        var x = llvm.insertGetStructElementPointer(
          of: e, typed: captures, index: i, at: insertionPoint)

        // Remote captures are passed dereferenced.
        if program.types.cast(c, to: RemoteType.self) != nil {
          // TODO see if this is still necessary after we have desugared projections.
          x = llvm.insertLoad(llvm.ptr, from: x, at: insertionPoint)
        }

        environment.append(x.erased)
      }

      let t = transpiledType(hyloType)
      return .init(function: f.erased, type: t.erased, environment: environment)
    }

    /// Returns the type of a transpiled function type corresponding to the given Arrow type in Hylo IR.
    ///
    /// - Note: return values are passed by pointer, and the captured environment is passed element-wise via pointers.
    func transpiledType(_ arrow: ConcreteTypeIdentity<Arrow>)
      -> SwiftyLLVM.FunctionType.UnsafeReference
    {
      let t = program.types[arrow]
      // Return value is passed as an extra out parameter by reference.
      var parameters: Int = t.inputs.count + 1

      // Environment is passed before explicit arguments.
      if t.environment != .void {
        parameters += t.captures(in: program).count
      }

      return llvm.functionType(
        from: Array(repeating: llvm.ptr.erased, count: parameters), to: llvm.void)
    }
  }
}

extension Program {
  /// Returns true iff `f` is a file-scoped 0-parameter function named `main`.
  func isModuleEntry(_ f: IRFunction) -> Bool {
    // TODO: add checks in the frontend to make sure its return type is either Void or Int or Int32
    guard case .lowered(let d) = f.name,
      parent(containing: d).isFile
    else { return false }

    guard let t = types.cast(type(assignedTo: d), to: Arrow.self),
      types[t].inputs.count == 0
    else { return false }

    return name(of: d)?.identifier == "main"
  }
}

/// The contents of an arrow.
private struct ArrowContents {

  /// A pointer to the underlying thin function.
  let function: SwiftyLLVM.AnyValue.UnsafeReference  // todo make AnyCallable.UnsafeReference

  /// The type `function`.
  let type: SwiftyLLVM.AnyType.UnsafeReference

  /// The arrow's environment.
  let environment: [SwiftyLLVM.AnyValue.UnsafeReference]

}

extension Arrow {
  /// Returns the list of captured types in the enviornment of `self`.
  func captures(in program: Program) -> [AnyTypeIdentity] {
    // todo see if we need to dealias/resolve type application here
    guard let tuple = program.types.cast(environment, to: Tuple.self) else {
      fatalError(
        "Expected environment of an arrow to be a tuple type, but got \(environment). Maybe we need to dealias the type or resolve a type application?"
      )
    }
    let captureTypes = program.types.members(of: tuple)
    assert(!captureTypes.isOpenEnded)
    return captureTypes.types
  }
}

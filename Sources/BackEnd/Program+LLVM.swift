import BigInt
import FrontEnd
import OrderedCollections
import SwiftyLLVM
import Utilities

extension Program {

  // Most methods in this extension accept a `XXXGenerationContext`, which represents the state
  // of the code generation algorithm, threaded to each sub-operation. This parameter is usually
  // named `ctx` and its documentation is typically omitted for concision.

  /// Compiles the IR of `m` for target `t`.
  ///
  /// - Requires: `m` has been lowered and all required passes have been run.
  public mutating func compileToLLVM(
    _ m: FrontEnd.Module.ID, target t: consuming TargetMachine
  ) throws -> SwiftyLLVM.Module {
    let product = SwiftyLLVM.Module(self[m].name, targetMachine: t)
    var context = ModuleGenerationContext(compiling: m, into: product)

    for f in self[m].ir.functions.values.indices {
      incorporate(f, in: &context)
    }

    return context.release()
  }

  /// Returns the name of the function corresponding to `f` in LLVM IR.
  ///
  /// The result is the mangled name of `f` unless its declaration has been annotated to specify a
  /// particular name (e.g., `@extern`).
  private func llvmName(
    function f: IRFunction.ID, in ctx: borrowing ModuleGenerationContext
  ) -> String {
    let v = self[ctx.hylo].ir[f].name
    if case .lowered(let d) = v, let n = externName(of: d) {
      return n
    } else {
      return mangled(f, of: ctx.hylo)
    }
  }

  /// Declares `f` and, if necessary, compiles its definition into the LLVM module being built.
  private mutating func incorporate(
    _ f: IRFunction.ID, in ctx: inout ModuleGenerationContext
  ) {
    // Don't compile generic functions.
    if !self[ctx.hylo].ir[f].isMonomorphic { return }
    // Don't re-compile functions.
    if !ctx.compiled.insert(f).inserted { return }

    // Get the declaraiton of LLVM function corresponding to `f`. It is possible that this function
    // has already been declared if it has been referred to by some code that was compiled first.
    let result = demandFunction(f, in: &ctx)
    incorporate(contentsOf: f, into: result, in: &ctx)

    // If `f` is the module's entry, define a "main" function that just applies it.
    if isEntry(f, of: ctx.hylo) {
      ctx.llvm.setLinkage(.private, for: result.llvm)
      defineMain(calling: result, in: &ctx)
    }
  }

  /// Compiles the contents of `source` into `result`.
  private mutating func incorporate(
    contentsOf source: IRFunction.ID, into result: FunctionMetadata,
    in ctx: inout ModuleGenerationContext
  ) {
    let ir = self[ctx.hylo].ir[source]

    // Nothing to do for functions having no definition.
    guard let sourceEntry = ir.entry else { return }

    // Initialize the code generation context.
    let region = DominatorTree(function: ir, controlFlow: ir.controlFlow())
    var nested = FunctionGenerationContext(
      compiling: ir, within: region, into: result, in: ctx)
    let e = nested.demandBasicBlock(sourceEntry)
    nested.insertionPoint = nested.module.llvm.endOf(e)

    // Configure the code generation context.
    if let p = result.output {
      setupParameterOrReturnValue(p, at: result.inputs.count, in: &nested)
    }
    for (i, p) in result.inputs.enumerated() {
      setupParameterOrReturnValue(p, at: i, in: &nested)
    }

    // Translate the instructions of the Hylo function to LLVM.
    for b in nested.dominance where !nested.factoredOut.contains(b) {
      guard let i = nested.ir.blocks[b].first else { continue }
      incorporate(from: i, in: &nested)
    }

    ctx = nested.release()
  }

  /// Compiles `start` and the following instructions.
  ///
  /// The LLVM basic block corresponding to the Hylo basic block containing `start` is created if
  /// necessary. The insertion point of `ctx` is moved at the end of that basic block and is not
  /// moved back to its original position.
  ///
  /// - Requires: All instructions dominating `start` have been incorporated.
  internal mutating func incorporate(
    from start: AnyInstructionIdentity, in ctx: inout FunctionGenerationContext
  ) {
    let v = ctx.demandBasicBlock(ctx.ir.block(defining: start))
    ctx.insertionPoint = ctx.module.llvm.endOf(v)

    var next: AnyInstructionIdentity? = start
    while let i = next {
      next = incorporate(i, in: &ctx)
    }
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: AnyInstructionIdentity, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    switch ctx.ir.tag(of: i) {
    case IRAccess.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRAccess.self), in: &ctx)
    case IRAccess.End.self:
      return ctx.ir.instruction(after: i)
    case IRAlloca.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRAlloca.self), in: &ctx)
    case IRApply.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRApply.self), in: &ctx)
    case IRAssumeState.self:
      return ctx.ir.instruction(after: i)
    case IRBranch.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRBranch.self), in: &ctx)
    case IRConditionalBranch.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRConditionalBranch.self), in: &ctx)
    case IRLoad.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRLoad.self), in: &ctx)
    case IRMemoryCopy.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRMemoryCopy.self), in: &ctx)
    case IRProject.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRProject.self), in: &ctx)
    case IRReturn.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRReturn.self), in: &ctx)
    case IRStore.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRStore.self), in: &ctx)
    case IRSubfield.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRSubfield.self), in: &ctx)
    case IRYield.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRYield.self), in: &ctx)
    case let s:
      fatalError("unexpected instruction \(s)")
    }
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRAccess.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let v = FrontEnd.IRValue.register(i.erased)
    ctx.value[v] = .some(ctx.value[s.source]!)
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRAlloca.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    assert(s.witness == nil, "unsupported dynamically sized alloca")

    let t = metadata(of: s.storage, in: &ctx.module)
    let x = ctx.module.llvm.insertAlloca(t.llvm, atEntryOf: ctx.llvm)
    ctx.module.llvm.setAlignment(t.layout.alignment, for: x)

    let v = IRValue.register(i.erased)
    ctx.value[v] = x.asAnyValue
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRApply.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    switch s.callee {
    case .function(let n, _, _):
      let f = demandFunction(n, in: &ctx.module)
      let x = insertArguments(s.arguments, forCalling: f, in: &ctx)
      insertCall(f, x, writingResultTo: s.result, in: &ctx)

    default:
      // TODO: Obtain function metadata from other values.
      fatalError()
    }

    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRBranch.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let a = ctx.demandBasicBlock(s.target)
    ctx.module.llvm.insertBr(to: a, at: ctx.insertionPoint!)
    return nil
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRConditionalBranch.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let a = ctx.demandBasicBlock(s.onSuccess)
    let b = ctx.demandBasicBlock(s.onFailure)
    ctx.module.llvm.insertCondBr(
      if: ctx.value[s.condition]!, then: a, else: b, at: ctx.insertionPoint!)
    return nil
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRLoad.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let t = metadata(of: ctx.ir.resolved(s.type)!.type, in: &ctx.module)
    let x = ctx.module.llvm.insertLoad(t.llvm, from: ctx.value[s.source]!, at: ctx.insertionPoint!)
    let v = IRValue.register(i.erased)
    ctx.value[v] = x.asAnyValue
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRMemoryCopy.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let t = metadata(of: ctx.ir.result(of: s.source)!.type, in: &ctx.module)

    let ptr = ctx.module.llvm.ptr
    let i32 = ctx.module.llvm.i32
    let memcpy = ctx.module.llvm.intrinsic(
      named: IntrinsicFunction.llvm.memcpy, for: [ptr.asAnyType, ptr.asAnyType, i32.asAnyType])!

    let x0 = codegen(s.target, in: &ctx).asAnyValue
    let x1 = codegen(s.source, in: &ctx).asAnyValue
    let x2 = i32.unsafe[].constant(t.layout.size).asAnyValue
    let x3 = ctx.module.llvm.i1.unsafe[].constant(0).asAnyValue
    _ = ctx.module.llvm.insertCall(
      memcpy, on: [x0, x1, x2, x3],
      at: ctx.insertionPoint!)

    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  ///
  /// Code dominated by `i` is compiled into a different function that is passed as a callback to
  /// the subscript being applied by `i`. The call to this subscript returns the identifier of the
  /// basic block to which control-flow should be transferred, if any.
  ///
  /// This method extends `ctx.factoredOut` with the basic blocks that have been compiled into the
  /// callback. These basic blocks cannot have been visited yet, since they are dominated by `i`.
  /// They shall not be incorporated into the function being compiled.
  internal mutating func incorporate(
    _ i: IRProject.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    // Compile the plateau following the project instruction.
    let (plateau, captures, covered) = definePlateau(dominatedBy: i, in: &ctx)

    let s = ctx.ir.at(i)
    switch s.callee {
    case .function(let n, _, _):
      let f = demandFunction(n, in: &ctx.module)
      var x = insertArguments(s.arguments, forCalling: f, in: &ctx)
      x.append(plateau.llvm.asAnyValue)
      x.append(captures.asAnyValue)

      // The call to the subscript's ramp returns with the identifier of the basic block to which
      // control flow should be transferred. This basic block must be a successor of one of the
      // blocks having been incorporated that is not dominated by `i`.
      let after = ctx.module.llvm.insertCall(f.llvm, on: x, at: ctx.insertionPoint!)
      let successors = ctx.ir.decode(covered).reduce(into: IRBlockSet()) { (s, a) in
        for b in ctx.ir.successors(of: a) where !covered.contains(b) { s.insert(b) }
      }

      // Compute the branches of a switch terminator redirecting control-flow.
      typealias Case = SwiftyLLVM.Module.SwitchCase
      let i32 = ctx.module.llvm.i32
      let cases = ctx.ir.decode(successors).map { (b: IRBlock.ID) -> Case in
        let n = i32.unsafe[].constant(b.rawValue).asAnyValue
        let b = ctx.demandBasicBlock(b)
        return (n, b)
      }

      if let (c, cs) = cases.headAndTail {
        // Insert the switch terminator, using the first case as a default branch.
        ctx.module.llvm.insertSwitch(on: after, cases: cs, default: c.1, at: ctx.insertionPoint!)
      } else {
        // If none of the blocks covered by the plateau has a successor, then the remainder of the
        // function has been incorporated to the plateau.
        assert(successors.isEmpty)
        if ctx.result.isPlateau {
          ctx.module.llvm.insertReturn(after, at: ctx.insertionPoint!)
        } else {
          insertReturn(in: &ctx)
        }
      }

    default:
      // TODO: Obtain function metadata from other values.
      fatalError()
    }

    return nil
  }

  /// Generates the LLVM IR code corresponding to `i`.
  ///
  /// If the return value of the function being built is passed by output parameter, this method
  /// assumes that this value has already been stored in the memory referred to that parameter it
  /// inserts `ret void`. Otherwise, the return value is loaded from its corresponding alloca
  /// before being returned.
  internal mutating func incorporate(
    _ i: IRReturn.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    insertReturn(in: &ctx)
    return nil
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRStore.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let x = codegen(s.value, in: &ctx)
    let y = ctx.value[s.target]!
    // TODO: alignment
    ctx.module.llvm.insertStore(x, to: y, at: ctx.insertionPoint!)
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRSubfield.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let t = ctx.ir.result(of: s.base)!.type

    let i32 = ctx.module.llvm.i32
    var indices = [i32.unsafe[].constant(0).asAnyValue]
    var u = t
    for p in s.path {
      let m = metadata(of: u, in: &ctx.module)
      indices.append(i32.unsafe[].constant(m.layout.propertyToField[p]).asAnyValue)
      u = storage(of: u, visibleFrom: ctx.module.hylo)![p]
    }

    let b = ctx.value[s.base]!
    let m = metadata(of: t, in: &ctx.module)
    let x = ctx.module.llvm.insertGetElementPointerInBounds(
      of: b, typed: m.llvm, indices: indices, at: ctx.insertionPoint!)

    let v = IRValue.register(i.erased)
    ctx.value[v] = x.asAnyValue
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRYield.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    // Compile the slide following the yield instruction.
    let (slide, captures) = defineSlide(dominatedBy: i, in: &ctx)

    // Call the plateau, which will call the slide.
    let instruction = ctx.ir.at(i)
    let control = ctx.module.llvm.insertCall(
      ctx.llvm.unsafe[].parameters[fromLast: 1].asAnyValue,
      typed: ctx.module.plateau.asAnyType,
      on: [
        // projected value
        ctx.value[instruction.projectee]!,
        // the plateau's environment
        ctx.llvm.unsafe[].parameters[fromLast: 0].asAnyValue,
        // the slide
        slide.llvm.asAnyValue,
        // the slide's environment
        captures.asAnyValue,
      ],
      at: ctx.insertionPoint!)

    // Return from the ramp with the result of the plateau.
    ctx.module.llvm.insertReturn(control, at: ctx.insertionPoint!)
    return nil
  }

  /// Returns the LLVM function corresponding to `f`, declaring it if necessary.
  ///
  /// If `f` is a subscript, the result is the function that represents its ramp, which accepts a
  /// caller plateau and its environment as extra parameters. Slides are declared during the code
  /// generation of a subscript and are typically never called directly from another context.
  private mutating func demandFunction(
    _ f: IRFunction.ID, in ctx: inout ModuleGenerationContext
  ) -> FunctionMetadata {
    let ir = self[ctx.hylo].ir[f]
    if let existing = ctx.functionMetadata[ir.name] {
      return existing
    }

    let name = llvmName(function: f, in: ctx)
    let signature = ir.signature()
    let maxFootprint = ctx.llvm.layout.pointerSize

    var parameters: [SwiftyLLVM.AnyType.UnsafeReference] = []
    var inputs: [FunctionMetadata.Parameter] = .init(
      minimumCapacity: signature.head.inputs.count + 1)

    // The input parameters of the IR function come first.
    for p in signature.head.inputs {
      let t = metadata(of: p.type, in: &ctx)

      // Parameters of size 0 are simply ignored.
      if t.layout.size == 0 {
        inputs.append(.init(type: t, convention: .erased))
      }

      // `let` and `sink` with a small footprint are passed into registers. Other parameters are
      // passed by reference.
      else if (t.layout.size <= maxFootprint) && AccessEffectSet.functional.contains(p.access) {
        inputs.append(.init(type: t, convention: .byValue(parameters.count)))
        parameters.append(t.llvm)
      } else {
        inputs.append(.init(type: t, convention: .byReference(parameters.count)))
        parameters.append(ctx.llvm.ptr.asAnyType)
      }
    }

    // If `f` is a subscript, then we compile it as a ramp. A ramp gets two extra parameters for
    // the caller's plateau and its environment.
    if signature.head.style == .bracketed {
      parameters.append(ctx.llvm.functionPointer.asAnyType)
      parameters.append(ctx.llvm.ptr.asAnyType)
      let t = ctx.llvm.functionType(from: parameters, to: ctx.llvm.i32.asAnyType)
      let v = ctx.llvm.declareFunction(name, t)
      let u = metadata(of: .void, in: &ctx)
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: u, convention: .erased))
    }

    // Otherwise, the return value depends on the size of its type.
    let o = metadata(of: signature.head.output, in: &ctx)

    // Can the result be erased?
    if o.layout.size == 0 {
      let t = ctx.llvm.functionType(from: parameters)
      let v = ctx.llvm.declareFunction(name, t)
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: o, convention: .erased))
    }

    // Can the result be returned by value?
    else if o.layout.size <= maxFootprint {
      let t = ctx.llvm.functionType(from: parameters, to: o.llvm)
      let v = ctx.llvm.declareFunction(name, t)
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: o, convention: .byValue(-1)))
    }

    // The result is returned by output parameter.
    else {
      let t = ctx.llvm.functionType(from: parameters + [o.llvm])
      let v = ctx.llvm.declareFunction(name, t)
      let n = parameters.count
      return FunctionMetadata(
        llvm: v, inputs: inputs, output: .init(type: o, convention: .byReference(n)))
    }
  }

  /// Configures `ctx` with so that code generation can handle uses of `p`, which is the `i`-th
  /// parameter of the function being compiled to LLVM.
  ///
  /// This method extends `ctx.value` so that it maps the representation of `p` in Hylo IR to its
  /// corresponding representation in LLVM IR. There are three cases to handle:
  ///
  /// * `p` has been erased, in which case it should map to a 0-byte alloca.
  /// * `p` is passed by value, in which case it should map to an alloca containing that value.
  /// * `p` is passed by reference, in which case it can be mapped directly.
  ///
  /// Instructions necessary to setup the mapping are inserted at the current entry point, which
  /// is assumed to be in the entry of the function being built.
  private func setupParameterOrReturnValue(
    _ p: FunctionMetadata.Parameter, at i: Int, in ctx: inout FunctionGenerationContext
  ) {
    let v = FrontEnd.IRValue.parameter(i)

    switch p.convention {
    case .erased:
      // `p` has been erased and can thus be represented by a 0-byte alloca.
      let x = ctx.module.llvm.insertAlloca(ctx.module.empty, at: ctx.insertionPoint!)
      ctx.value[v] = x.asAnyValue

    case .byValue(let j):
      // The argument to `p` is passed by value. Store it into an alloca so that it can be read
      // from memory in subsequent operations. Memory to register promotion (mem2reg) will get rid
      // of needless load/stores later.
      let t = (j >= 0) ? ctx.result.inputs[j].type : ctx.result.output!.type
      let x = ctx.module.llvm.insertAlloca(t.llvm, at: ctx.insertionPoint!)
      ctx.module.llvm.setAlignment(t.layout.alignment, for: x)
      if j >= 0 {
        ctx.module.llvm.insertStore(
          ctx.llvm.unsafe[].parameters[j], to: x, at: ctx.insertionPoint!)
        // TODO: Alignment
      }
      ctx.value[v] = x.asAnyValue

    case .byReference(let j):
      // The argument to `p` is passed by reference. It is already in memory.
      ctx.value[v] = ctx.llvm.unsafe[].parameters[j].asAnyValue
    }
  }

  /// Returns the representations of `arguments`, which are passed to `callee`, in LLVM IR.
  ///
  /// The result contains a LLVM IR value for each non-erased parameter of the callee, computed
  /// using `codegen(_:in:)`. Arguments passed by value are loaded from memory whereas no further
  /// transformation is applied on arguments passed by reference.
  private mutating func insertArguments<T: Collection<FrontEnd.IRValue>>(
    _ arguments: T, forCalling callee: FunctionMetadata, in ctx: inout FunctionGenerationContext
  ) -> [SwiftyLLVM.AnyValue.UnsafeReference] {
    var actual: [SwiftyLLVM.AnyValue.UnsafeReference] = []
    for (p, a) in zip(callee.inputs, arguments) {
      let l = codegen(a, in: &ctx)
      switch p.convention {
      case .erased:
        continue
      case .byValue:
        let x = ctx.module.llvm.insertLoad(p.type.llvm, from: l, at: ctx.insertionPoint!)
        // TODO: alignment
        actual.append(x.asAnyValue)
      case .byReference:
        actual.append(l)
      }
    }
    return actual
  }

  /// Generates the LLVM IR code for applying `callee` to `arguments`, writing the result of the
  /// call to the storage represented by `result`.
  private mutating func insertCall(
    _ callee: FunctionMetadata,
    _ arguments: consuming [SwiftyLLVM.AnyValue.UnsafeReference],
    writingResultTo result: FrontEnd.IRValue,
    in ctx: inout FunctionGenerationContext
  ) {
    switch callee.output!.convention {
    case .erased:
      _ = ctx.module.llvm.insertCall(
        callee.llvm, on: arguments, at: ctx.insertionPoint!)

    case .byValue:
      let x = ctx.module.llvm.insertCall(
        callee.llvm, on: arguments, at: ctx.insertionPoint!)
      let o = codegen(result, in: &ctx)
      ctx.module.llvm.insertStore(x, to: o, at: ctx.insertionPoint!)
      // TODO: Alignment

    case .byReference:
      let o = codegen(result, in: &ctx)
      arguments.append(o)
      _ = ctx.module.llvm.insertCall(
        callee.llvm, on: arguments, at: ctx.insertionPoint!)
    }
  }

  /// Generates the LLVM IR code for returning from the function being compiled.
  private func insertReturn(in ctx: inout FunctionGenerationContext) {
    switch ctx.result.output!.convention {
    case .erased, .byReference:
      ctx.module.llvm.insertReturn(at: ctx.insertionPoint!)

    case .byValue:
      let t = ctx.result.output!.type.llvm
      let x = ctx.value[ctx.ir.returnRegister!]!
      let y = ctx.module.llvm.insertLoad(t, from: x, at: ctx.insertionPoint!)
      // TODO: alignment
      ctx.module.llvm.insertReturn(y, at: ctx.insertionPoint!)
    }
  }

  /// Defines a "main" function calling `f`, which is the module's entry point.
  ///
  /// This method creates a function named "main" acting as a program entry point. This function
  /// wraps a call to `f`, which represents the entry point of an executable Hylo module, and
  /// returns the exit status of the program.
  ///
  /// `f` is a function linked privately in the module, taking no parameter and returning either
  /// `Hylo.Int32` or `Hylo.Void`. In the former case, the main function returns the result of `f`.
  /// Otherwise, it returns 0. Note that `f` may terminate the execution of the program before
  /// returning to the main function (e.g., due to a trap).
  private mutating func defineMain(
    calling f: FunctionMetadata, in ctx: inout ModuleGenerationContext
  ) {
    let i32 = ctx.llvm.i32
    let m = ctx.llvm.declareFunction("main", ctx.llvm.functionType(from: [], to: i32))
    let e = ctx.llvm.appendBlock(to: m)
    let p = ctx.llvm.endOf(e)
    let r = ctx.llvm.insertCall(f.llvm, on: [], at: p)

    // `f` returns an exit status iff its return type has a non-zero size, in which case we can
    // assume it is an instance of `Hylo.Int32`.
    if f.output!.type.layout.size > 0 {
      let v = ctx.llvm.insertExtractValue(from: r, at: 0, at: p)
      ctx.llvm.insertReturn(v, at: p)
    } else {
      ctx.llvm.insertReturn(i32.unsafe[].zero, at: p)
    }
  }

  /// Returns the representation of `v` in LLVM IR.
  private mutating func codegen(
    _ v: FrontEnd.IRValue, in ctx: inout FunctionGenerationContext
  ) -> SwiftyLLVM.AnyValue.UnsafeReference {
    switch v {
    case .integer(let n, let t):
      return codegen(integer: n, instanceOf: t, in: &ctx.module)
    case .register:
      return ctx.value[v]!
    default:
      fatalError("no LLVM representation of type '\(show(v))'")
    }
  }

  /// Returns a LLVM IR constant equivalent to `n`, which is an instance of an integer type `t`.
  private mutating func codegen(
    integer n: BigInt, instanceOf t: MachineType.ID, in ctx: inout ModuleGenerationContext
  ) -> SwiftyLLVM.AnyValue.UnsafeReference {
    let u = metadata(of: t, in: &ctx)
    let t = IntegerType.UnsafeReference(u.llvm)!
    if n == 0 {
      return t.unsafe[].zero.asAnyValue
    } else {
      return t.unsafe[].constant(words: n.words.map(UInt64.init(_:))).asAnyValue
    }
  }

  /// Returns the LLVM type corresponding to the Hylo type `t`, using `compute` to determine its
  /// properties if necessary.
  ///
  /// `compute` accepts projections of this method's arguments along with the mangled name of `t`,
  /// and it returns the metadata of `t`. This result is memoized and returned for all subsequent
  /// calls to this method with the same type and ctx.
  private mutating func metadata<T: TypeIdentity>(
    of t: T, in ctx: inout ModuleGenerationContext,
    computedWith compute: (inout Self, inout ModuleGenerationContext, T, String) -> TypeMetadata
  ) -> TypeMetadata {
    let n = mangled(t)
    if let memoized = ctx.typeMetadata[n] {
      return memoized
    } else {
      let result = compute(&self, &ctx, t, n)
      ctx.typeMetadata[n] = result
      return result
    }
  }

  /// Returns the LLVM type corresponding of the Hylo type `t`.
  internal mutating func metadata(
    of t: AnyTypeIdentity, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    switch types.tag(of: t) {
    case MachineType.self:
      metadata(of: types.castUnchecked(t, to: MachineType.self), in: &ctx)
    case Struct.self:
      metadata(of: types.castUnchecked(t, to: Struct.self), in: &ctx)
    case Tuple.self:
      metadata(of: types.castUnchecked(t, to: Tuple.self), in: &ctx)
    default:
      unimplemented("no LLVM representation of type '\(show(t))'")
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: MachineType.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      let v = switch program.types[t] {
      case .i(let width):
        ctx.llvm.integerType(Int(width)).asAnyType
      case .word:
        ctx.llvm.iptr.asAnyType
      case .ptr:
        ctx.llvm.ptr.asAnyType
      default:
        unimplemented("no LLVM representation of type '\(program.show(t))'")
      }

      let s = ctx.llvm.layout.storageSize(of: v)
      let a = ctx.llvm.layout.preferredAlignment(of: v)
      let l = ConcreteLayout(fields: [], propertyToField: [], size: s, alignment: a)
      return TypeMetadata(llvm: v, layout: l)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Struct.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      // TODO: Resilience
      let m = program.types[t].declaration.module
      let properties = program.storage(of: t.erased, visibleFrom: m)!
      return program.metadata(record: n, rows: properties, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Tuple.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      let (properties, isOpenEnded) = program.types.members(of: t)
      precondition(!isOpenEnded, "no LLVM representation of type '\(program.show(t))'")
      return program.metadata(record: n, rows: properties, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of a record type having the given name and rows.
  private mutating func metadata(
    record name: String, rows: [AnyTypeIdentity], in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    let layout = record(rows: rows, in: &ctx)
    let definition = ctx.llvm.structType(named: name, layout.fields, packed: true).asAnyType

    assert(ctx.llvm.layout.storageSize(of: definition) <= layout.size)
    assert(ctx.llvm.layout.abiAlignment(of: definition) <= layout.alignment)
    return TypeMetadata(llvm: definition, layout: layout)
  }

  /// Returns the standard layout of a record type having the given rows.
  private mutating func record(
    rows: [AnyTypeIdentity], in ctx: inout ModuleGenerationContext
  ) -> ConcreteLayout {
    let rs = rows.map({ (u) in metadata(of: u, in: &ctx) })
    let ps = rows.indices.sorted { (a, b) in
      let lhs = rs[a].layout.alignment
      let rhs = rs[b].layout.alignment
      return (rhs < lhs) || ((lhs == rhs) && (a < b))
    }

    var fields: [SwiftyLLVM.AnyType.UnsafeReference] = []
    var rowToField = Array(repeating: -1, count: rs.count)
    var size = 0

    for p in ps where rs[p].layout.size > 0 {
      // There should be no need for padding bits.
      assert(size.rounded(upToNearestMultipleOf: rs[p].layout.alignment) == size)

      rowToField[p] = fields.count
      fields.append(rs[p].llvm)
      size += rs[p].layout.size
    }

    let a = rs.last?.layout.alignment ?? 1
    return ConcreteLayout(fields: fields, propertyToField: rowToField, size: size, alignment: a)
  }

}

import BigInt
import FrontEnd
import OrderedCollections
import SwiftyLLVM
import Utilities

/// A Hylo module.
internal typealias HyloModule = FrontEnd.Module

/// A SwiftyLLVM module.
internal typealias LLVMModule = SwiftyLLVM.Module

/// A reference to a type in LLVM IR.
internal typealias LLVMType = SwiftyLLVM.AnyType.UnsafeReference

/// A reference to a value in LLVM IR.
internal typealias LLVMValue = SwiftyLLVM.AnyValue.UnsafeReference

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

  /// Returns the name of the global corresponding to `g` in LLVM IR.
  ///
  /// The result is the mangled name of `g` unless its declaration has been annotated to specify a
  /// particular name (e.g., `@extern`).
  private func llvmName(global g: IRGlobal.Name) -> String {
    if case .lowered(let d) = g, let n = externName(of: .init(d)) {
      return n
    } else {
      return mangled(g)
    }
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
      return mangled(v)
    }
  }

  /// Declares `f` and, if necessary, compiles its definition into the LLVM module being built.
  private mutating func incorporate(
    _ f: IRFunction.ID, in ctx: inout ModuleGenerationContext
  ) {
    // Don't compile generic functions.
    if !self[ctx.hylo].ir[f].isMonomorphic { return }
    // Don't compile functions without a definition.
    if !self[ctx.hylo].ir[f].isDefined { return }
    // Don't re-compile functions.
    if !ctx.compiled.insert(f).inserted { return }

    // Get the declaraiton of LLVM function corresponding to `f`. It is possible that this function
    // has already been declared if it has been referred to by some code that was compiled first.
    let result = demandFunction(f, in: &ctx)
    incorporate(contentsOf: f, into: result, in: &ctx)

    // If `f` is the module's entry, define a "main" function that just applies it.
    if isEntry(f, of: ctx.hylo) {
      ctx.llvm.setLinkage(.private, for: result.value)
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
    if let p = result.prototype.mapping.output {
      setupParameterOrReturnValue(p, at: result.prototype.mapping.inputs.count, in: &nested)
    }
    for (i, p) in result.prototype.mapping.inputs.enumerated() {
      setupParameterOrReturnValue(p, at: i, in: &nested)
    }

    // Translate the instructions of the Hylo function to LLVM.
    let included = blocksToIncorporate(ir)
    for b in nested.dominance where included.contains(b) && !nested.factoredOut.contains(b) {
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
    case IRCase.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRCase.self), in: &ctx)
    case IRCase.End.self:
      return ctx.ir.instruction(after: i)
    case IRConditionalBranch.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRConditionalBranch.self), in: &ctx)
    case IRGlobalAccess.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRGlobalAccess.self), in: &ctx)
    case IRLoad.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRLoad.self), in: &ctx)
    case IRMemoryCopy.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRMemoryCopy.self), in: &ctx)
    case IRPlaceCast.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRPlaceCast.self), in: &ctx)
    case IRProject.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRProject.self), in: &ctx)
    case IRProperty.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRProperty.self), in: &ctx)
    case IRReturn.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRReturn.self), in: &ctx)
    case IRStore.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRStore.self), in: &ctx)
    case IRSubfield.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRSubfield.self), in: &ctx)
    case IRWitnessTable.self:
      return incorporate(ctx.ir.castUnchecked(i, to: IRWitnessTable.self), in: &ctx)
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
    ctx.value[v] = x.v
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRApply.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)

    // Is the call direct?
    if case .function(let n, _) = s.callee {
      let f = demandFunction(named: n, in: &ctx.module)
      let x = insertArguments(s.arguments, mappedWith: f.prototype.mapping, in: &ctx)
      insertCall(applying: f, to: x, writingResultTo: s.result, in: &ctx)
    }

    // Is the call indirect?
    else {
      let f = codegen(s.callee, in: &ctx)
      let a = types.seenAsTermAbstraction(ctx.ir.result(of: s.callee)!.type)!
      let p = prototype(types[a], in: &ctx.module)
      let x = insertArguments(s.arguments, mappedWith: p.mapping, in: &ctx)
      insertCall(applying: f, describedBy: p, to: x, writingResultTo: s.result, in: &ctx)
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
    _ i: IRCase.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let m = metadata(of: ctx.ir.result(of: s.source)!.type, in: &ctx.module)
    let t = StructType.UnsafeReference(m.llvm)!

    let x = ctx.module.llvm.insertGetStructElementPointer(
      of: ctx.value[s.source]!, typed: t, index: 1, at: ctx.insertionPoint!)
    let v = IRValue.register(i.erased)
    ctx.value[v] = x.v
    return ctx.ir.instruction(after: i.erased)
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
    _ i: IRGlobalAccess.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let x = demandGlobal(s.source, in: &ctx.module)
    let v = IRValue.register(i.erased)
    ctx.value[v] = x.v
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRLoad.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let t = metadata(of: ctx.ir.resolved(s.type)!.type, in: &ctx.module)
    let x = ctx.module.llvm.insertLoad(t.llvm, from: ctx.value[s.source]!, at: ctx.insertionPoint!)
    let v = IRValue.register(i.erased)
    ctx.value[v] = x.v
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRMemoryCopy.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let t = metadata(of: ctx.ir.result(of: s.source)!.type, in: &ctx.module)
    let n = t.layout.size.fixed ?? fatalError("unexpected dynamic size")

    let ptr = ctx.module.llvm.ptr
    let i32 = ctx.module.llvm.i32
    let memcpy = ctx.module.llvm.intrinsic(
      named: IntrinsicFunction.llvm.memcpy, for: [ptr.t, ptr.t, i32.t])!

    let x0 = codegen(s.target, in: &ctx).v
    let x1 = codegen(s.source, in: &ctx).v
    let x2 = i32.unsafe[].constant(n).v
    let x3 = ctx.module.llvm.i1.unsafe[].constant(0).v
    _ = ctx.module.llvm.insertCall(
      memcpy, on: [x0, x1, x2, x3],
      at: ctx.insertionPoint!)

    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRPlaceCast.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)
    let v = FrontEnd.IRValue.register(i.erased)
    ctx.value[v] = .some(ctx.value[s.source]!)
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  ///
  /// The instruction is compiled as a direct call iff the subscriptsubscript being applied is an
  /// addressor. Otherwise, code dominated by `i` is compiled into a different function that is
  /// passed as a callback to the subscript. The call to this subscript returns the identifier of
  /// the basic block to which control-flow should be transferred, if any.
  ///
  /// This method extends `ctx.factoredOut` with the basic blocks that have been compiled into the
  /// callback. These basic blocks cannot have been visited yet, since they are dominated by `i`.
  /// They shall not be incorporated into the function being compiled.
  internal mutating func incorporate(
    _ i: IRProject.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)

    // Is the callee an addressor?
    if let n = seenAsAddressor(s.callee, in: ctx) {
      let f = demandFunction(named: n, in: &ctx.module)
      let x = insertArguments(s.arguments, mappedWith: f.prototype.mapping, in: &ctx)
      let y = ctx.module.llvm.insertCall(f.value, on: x, at: ctx.insertionPoint!)
      _ = y
      fatalError()
    }

    // Otherwise, compile the plateau following the project instruction.
    let (plateau, captures, covered) = definePlateau(dominatedBy: i, in: &ctx)

    switch s.callee {
    case .function(let n, _):
      let f = demandFunction(named: n, in: &ctx.module)
      var x = insertArguments(s.arguments, mappedWith: f.prototype.mapping, in: &ctx)
      x.append(plateau.value.v)
      x.append(captures.v)

      // The call to the subscript's ramp returns with the identifier of the basic block to which
      // control flow should be transferred. This basic block must be a successor of one of the
      // blocks having been incorporated that is not dominated by `i`.
      let after = ctx.module.llvm.insertCall(f.value, on: x, at: ctx.insertionPoint!)
      let successors = covered.elements.reduce(into: IRBlockSet()) { (s, a) in
        for b in ctx.ir.successors(of: a) where !covered.contains(b) { s.insert(b) }
      }

      // Compute the branches of a switch terminator redirecting control-flow.
      typealias Case = SwiftyLLVM.Module.SwitchCase
      let i32 = ctx.module.llvm.i32
      let cases = successors.elements.map { (b: IRBlock.ID) -> Case in
        let n = i32.unsafe[].constant(b.rawValue).v
        let b = ctx.demandBasicBlock(b)
        return (n, b)
      }

      if let (c, cs) = cases.headAndTail {
        // Insert the switch terminator, using the first case as a default branch.
        ctx.module.llvm.insertSwitch(on: after, cases: cs, default: c.1, at: ctx.insertionPoint!)
      } else {
        // If none of the blocks covered by the plateau has a successor, then the remainder of the
        // function has been incorporated into the plateau.
        assert(successors.isEmpty)
        if ctx.result.isPlateau || ctx.result.isRamp {
          ctx.module.llvm.insertReturn(after, at: ctx.insertionPoint!)
        } else {
          // If we are the ramp of a subscript we should also return.
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
  internal mutating func incorporate(
    _ i: IRProperty.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)

    // Compute the LLVM types of the whole and its part.
    let recordHyloType = ctx.ir.result(of: s.record)!.type
    let w = metadata(of: recordHyloType, in: &ctx.module)
    let p = typeOfProperty(declaredBy: s.property, withType: s.propertyType, in: &ctx.module)

    // If the whole is a witness table, the property is a requirement of the trait for which the
    // table is witnessing a conformance.
    if let (concept, _) = types.seenAsTraitApplication(recordHyloType) {
      // The contents of a witness table follow the ordering of its requirements.
      let index = requirements(of: concept).index(of: s.property)!
      let whole = codegen(s.record, in: &ctx)
      let part = ctx.module.llvm.insertGetElementPointerInBounds(
        of: whole, typed: w.llvm,
        indices: [0, index], indexType: ctx.module.llvm.i32,
        at: ctx.insertionPoint!)

      let x = ctx.module.llvm.insertLoad(p, from: part, at: ctx.insertionPoint!)
      let v = FrontEnd.IRValue.register(i.erased)
      ctx.value[v] = x.v
    }

    // Otherwise, the property is a public property of some resilient type.
    else {
      fatalError("TODO: resilient records")
    }

    return ctx.ir.instruction(after: i.erased)
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
    var indices = [i32.unsafe[].constant(0).v]
    var u = t
    for p in s.path {
      let m = metadata(of: u, in: &ctx.module)
      indices.append(i32.unsafe[].constant(m.layout.propertyToField[p]).v)
      u = fields(of: u, visibleFrom: ctx.module.hylo)![p]
    }

    let b = ctx.value[s.base]!
    let m = metadata(of: t, in: &ctx.module)
    let x = ctx.module.llvm.insertGetElementPointerInBounds(
      of: b, typed: m.llvm, indices: indices, at: ctx.insertionPoint!)

    let v = IRValue.register(i.erased)
    ctx.value[v] = x.v
    return ctx.ir.instruction(after: i.erased)
  }

  /// Generates the LLVM IR code corresponding to `i`.
  internal mutating func incorporate(
    _ i: IRWitnessTable.ID, in ctx: inout FunctionGenerationContext
  ) -> AnyInstructionIdentity? {
    let s = ctx.ir.at(i)

    let entries = s.operands.map { (x) in
      codegen(x, in: &ctx)
    }

    let tableType = metadata(of: s.witnessType, in: &ctx.module)
    let table = ctx.module.llvm.structConstant(
      of: StructType.UnsafeReference(tableType.llvm)!, aggregating: entries)

    let v = IRValue.register(i.erased)
    ctx.value[v] = table.v
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

    let (plateau, environment) = ctx.insertExtractPlateau()
    let control = ctx.module.llvm.insertCall(
      plateau, typed: ctx.module.plateau.t,
      on: [
        // projected value
        ctx.value[instruction.projectee]!,
        // the plateau's environment
        environment,
        // the slide
        slide.value.v,
        // the slide's environment
        captures.v,
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

    let p = prototype(signature.head, in: &ctx)
    let v = ctx.llvm.declareFunction(name, p.signature)
    setupAttributes(of: v, compiledFrom: f, in: &ctx)

    let m = FunctionMetadata(prototype: p, value: v, isRamp: ir.isSubscript)
    ctx.functionMetadata[ir.name] = m
    return m
  }

  /// Returns the result of `demandFunction(_:in:)` with the identity of `f`, which is declared in
  /// the module being compiled.
  private mutating func demandFunction(
    named f: IRFunction.Name, in ctx: inout ModuleGenerationContext
  ) -> FunctionMetadata {
    let k = self[ctx.hylo].ir.identity(function: f)!
    return demandFunction(k, in: &ctx)
  }

  /// Returns the prototype of a LLVM IR function corresponding to a Hylo IR function whose
  /// signature is `a`.
  ///
  /// The result is computed by determining how the parameters of the Hylo IR function should be
  /// represented in the corresponding LLVM IR function. Some parameters may be erased and, in the
  /// case of subscripts, some additional parameters may be inserted.
  ///
  /// - Requires: `a` has an empty environment.
  private mutating func prototype(
    _ a: Arrow, in ctx: inout ModuleGenerationContext
  ) -> Prototype {
    assert(a.environment == .void)

    let maxFootprint = ctx.llvm.layout.pointerSize
    var inputMap: [Prototype.Parameter] = .init(minimumCapacity: a.inputs.count + 1)
    var inputs: [LLVMType] = []

    // The input parameters of the IR function come first.
    for p in a.inputs {
      let t = metadata(of: p.type, in: &ctx)

      // Parameters of size 0 are simply ignored.
      if t.layout.size == 0 {
        inputMap.append(.init(type: t, convention: .erased))
      }

      // `let` and `sink` with a small footprint are passed into registers. Other parameters are
      // passed by reference.
      else if (t.layout.size <= maxFootprint) && AccessEffectSet.functional.contains(p.access) {
        inputMap.append(.init(type: t, convention: .byValue(inputs.count)))
        inputs.append(t.llvm)
      } else {
        inputMap.append(.init(type: t, convention: .byReference(inputs.count)))
        inputs.append(ctx.llvm.ptr.t)
      }
    }

    // Is `f` a subscript?
    if a.style == .bracketed {
      // Otherwise, `f` is compiled as a ramp, which accepts two extra parameters for the caller's
      // plateau and its environment.
      inputs.append(ctx.llvm.functionPointer.t)
      inputs.append(ctx.llvm.ptr.t)

      let u = metadata(of: .void, in: &ctx)
      let t = ctx.llvm.functionType(from: inputs, to: ctx.llvm.i32.t)
      return .init(
        signature: t,
        mapping: .init(inputs: inputMap, output: .init(type: u, convention: .erased)))
    }

    // Otherwise, the return value depends on the size of its type.
    else {
      let o = metadata(of: a.output, in: &ctx)

      // Can the result be erased?
      if o.layout.size == 0 {
        let t = ctx.llvm.functionType(from: inputs)
        return .init(
          signature: t,
          mapping: .init(inputs: inputMap, output: .init(type: o, convention: .erased)))
      }

      // Can the result be returned by value?
      else if let n = o.layout.size.fixed, n <= maxFootprint {
        let t = ctx.llvm.functionType(from: inputs, to: o.llvm)
        return .init(
          signature: t,
          mapping: .init(inputs: inputMap, output: .init(type: o, convention: .byValue(-1))))
      }

      // The result is returned by output parameter.
      else {
        let n = inputs.count
        let t = ctx.llvm.functionType(from: Array(inputs, terminatedBy: ctx.llvm.ptr.t))
        return .init(
          signature: t,
          mapping: .init(inputs: inputMap, output: .init(type: o, convention: .byReference(n))))
      }
    }
  }

  /// Configures the attributes of `g`, which is the LLVM function to which `f` compiles.
  private mutating func setupAttributes(
    of g: Function.UnsafeReference, compiledFrom f: IRFunction.ID,
    in ctx: inout ModuleGenerationContext
  ) {
    if isPrivate(self[ctx.hylo].ir[f].name, in: ctx.hylo) {
      assert(self[ctx.hylo].ir[f].isDefined)
      ctx.llvm.setLinkage(.private, for: g)
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
    _ p: Prototype.Parameter, at i: Int, in ctx: inout FunctionGenerationContext
  ) {
    let v = FrontEnd.IRValue.parameter(i)

    switch p.convention {
    case .erased:
      // `p` has been erased and can thus be represented by a 0-byte alloca.
      let x = ctx.module.llvm.insertAlloca(ctx.module.empty, at: ctx.insertionPoint!)
      ctx.value[v] = x.v

    case .byValue(let j):
      // The argument to `p` is passed by value. Store it into an alloca so that it can be read
      // from memory in subsequent operations. Memory to register promotion (mem2reg) will get rid
      // of needless load/stores later.
      let m = ctx.result.prototype.mapping
      let t = (j >= 0) ? m.inputs[j].type : m.output!.type
      let x = ctx.module.llvm.insertAlloca(t.llvm, at: ctx.insertionPoint!)
      ctx.module.llvm.setAlignment(t.layout.alignment, for: x)
      if j >= 0 {
        ctx.module.llvm.insertStore(
          ctx.llvm.unsafe[].parameters[j], to: x, at: ctx.insertionPoint!)
        // TODO: Alignment
      }
      ctx.value[v] = x.v

    case .byReference(let j):
      // The argument to `p` is passed by reference. It is already in memory.
      ctx.value[v] = ctx.llvm.unsafe[].parameters[j].v
    }
  }

  /// Returns the set of blocks whose instructions have to be incorporated in the LLVM function
  /// representing the entry of `ir`.
  ///
  /// If `ir` is a subscript, then the result contains all the basic blocks that are part of its
  /// ramp. Otherwise, the result is the set of basic blocks in `ir`.
  private func blocksToIncorporate(_ ir: IRFunction) -> IRBlockSet {
    if ir.isSubscript, let e = ir.entry {
      var result = IRBlockSet()
      var work = [e]
      while let b = work.popLast() {
        result.insert(b)
        if !ir.contains(in: b, IRYield.self) {
          work.append(contentsOf: ir.successors(of: b).filter({ (n) in !result.contains(n) }))
        }
      }
      return result
    } else {
      return .init(ir.blocks.addresses)
    }
  }

  /// Returns the global LLVM variable corresponding to `g`, declaring it if necessary.
  private mutating func demandGlobal(
    _ g: IRGlobal, in ctx: inout ModuleGenerationContext
  ) -> SwiftyLLVM.GlobalVariable.UnsafeReference {
    let name = llvmName(global: g.name)
    if let existing = ctx.llvm.global(named: name) {
      return existing
    }

    switch g.name {
    case .lowered:
      fatalError("TODO: global bindings")

    case .witness(let t):
      // TODO: type arguments/parameters
      // TODO: witnesses of opaque types

      // Declare the symbol.
      let storage = ctx.llvm.structType(ctx.typeWitnessHeader)
      let symbol = ctx.llvm.declareGlobalVariable(name, storage)
      ctx.llvm.setLinkage(.private, for: symbol)

      // The symbol is defined iff the layout of the type is fixed, so that it may be inlined in
      // the module. Otherwise, the witness is for a type whose layout is defined externally.
      let m = metadata(of: t, in: &ctx)
      guard let s = m.layout.size.fixed else { return symbol }

      let fields: [LLVMValue] = [
        demandGlobalString(show(t), in: &ctx).v,
        ctx.llvm.i32.unsafe[].constant(s).v,
        ctx.llvm.i16.unsafe[].constant(m.layout.alignment).v,
        ctx.llvm.i16.unsafe[].zero.v,
      ]

      let alignment = ctx.llvm.layout.preferredAlignment(of: storage)
      ctx.llvm.setAlignment(alignment, for: symbol)

      let initializer = ctx.llvm.structConstant(of: storage, aggregating: fields)
      ctx.llvm.setInitializer(initializer, for: symbol)
      ctx.llvm.setGlobalConstant(true, for: symbol)

      return symbol
    }
  }

  private func demandGlobalString(
    _ s: String, in ctx: inout ModuleGenerationContext
  ) -> LLVMValue {
    // Did we compute the representation already?
    if let v = ctx.strings[s] { return v }

    let iptr = ctx.llvm.iptr
    let payloadSize = s.utf8.count
    let pointerSize = ctx.llvm.layout.pointerSize

    // Do the contents fit inline storage?
    if (payloadSize < pointerSize) && (pointerSize <= 8) {
      var units = UInt64(truncatingIfNeeded: payloadSize) << 2
      for (i, u) in s.utf8.enumerated() {
        units |= UInt64(u) << (i + 1) * 8
      }
      let v = iptr.unsafe[].constant(units).v
      ctx.strings[s] = v
      return v
    }

    // Contents must be allocated in static memory.
    let name = String(FNV1.hash(s.utf8, into: FNV1.u128()).state, radix: 36)
    let payload = ctx.llvm.arrayConstant(bytes: s.utf8)
    let storage = ctx.llvm.structType([iptr.t, iptr.t, payload.unsafe[].type])
    let symbol = ctx.llvm.declareGlobalVariable("str_\(name)", storage)
    ctx.llvm.setLinkage(.private, for: symbol)

    // Guarantee minimum alignment of 4 so that we can reserve low bits for tagging.
    let alignment = max(ctx.llvm.layout.preferredAlignment(of: storage), 4)
    ctx.llvm.setAlignment(alignment, for: symbol)

    let count = iptr.unsafe[].constant(payloadSize).v
    let initializer = ctx.llvm.structConstant(
      of: storage, aggregating: [count, count, payload.v])
    ctx.llvm.setInitializer(initializer, for: symbol)
    ctx.llvm.setGlobalConstant(true, for: symbol)

    let v = ctx.llvm.constantPointerToInteger(bitPattern: symbol)
    let w = ctx.llvm.constantAdd(v, iptr.unsafe[].constant(0b11))
    ctx.strings[s] = w
    return w
  }

  /// Returns the representations of `arguments`, which are passed to `callee`, in LLVM IR.
  ///
  /// The result contains a LLVM IR value for each non-erased parameter of the callee, computed
  /// using `codegen(_:in:)`. Arguments passed by value are loaded from memory whereas no further
  /// transformation is applied on arguments passed by reference.
  private mutating func insertArguments<T: Collection<FrontEnd.IRValue>>(
    _ arguments: T, mappedWith mapping: Prototype.Mapping,
    in ctx: inout FunctionGenerationContext
  ) -> [LLVMValue] {
    var actual: [LLVMValue] = []
    for (p, a) in zip(mapping.inputs, arguments) {
      let l = codegen(a, in: &ctx)
      switch p.convention {
      case .erased:
        continue
      case .byValue:
        let x = ctx.module.llvm.insertLoad(p.type.llvm, from: l, at: ctx.insertionPoint!)
        // TODO: alignment
        actual.append(x.v)
      case .byReference:
        actual.append(l)
      }
    }
    return actual
  }

  /// Generates the LLVM IR code for applying `callee` to `xs`, writing the result of the call to
  /// the storage represented by `result`.
  private mutating func insertCall(
    applying callee: FunctionMetadata, to xs: consuming [LLVMValue],
    writingResultTo result: FrontEnd.IRValue,
    in ctx: inout FunctionGenerationContext
  ) {
    insertCall(
      applying: callee.value, describedBy: callee.prototype, to: xs,
      writingResultTo: result, in: &ctx)
  }

  /// Generates the LLVM IR code for applying `callee`, which is described by `shape`, to `xs`,
  /// writing the result of the call to the storage represented by `result`.
  private mutating func insertCall<F: SwiftyLLVM.IRValue>(
    applying callee: F.UnsafeReference, describedBy shape: Prototype, to xs: consuming [LLVMValue],
    writingResultTo result: FrontEnd.IRValue,
    in ctx: inout FunctionGenerationContext
  ) {
    switch shape.mapping.output!.convention {
    case .erased:
      _ = ctx.module.llvm.insertCall(
        callee.v, typed: shape.signature.t, on: xs, at: ctx.insertionPoint!)

    case .byValue:
      let x = ctx.module.llvm.insertCall(
        callee.v, typed: shape.signature.t, on: xs, at: ctx.insertionPoint!)
      let o = codegen(result, in: &ctx)
      ctx.module.llvm.insertStore(x, to: o, at: ctx.insertionPoint!)
      // TODO: Alignment

    case .byReference:
      let o = codegen(result, in: &ctx)
      xs.append(o)
      _ = ctx.module.llvm.insertCall(
        callee.v, typed: shape.signature.t, on: xs, at: ctx.insertionPoint!)
    }
  }

  /// Generates the LLVM IR code for returning from the function being compiled.
  private func insertReturn(in ctx: inout FunctionGenerationContext) {
    let p = ctx.module.functionMetadata[ctx.ir.name]!.prototype.mapping.output!

    switch p.convention {
    case .erased, .byReference:
      ctx.module.llvm.insertReturn(at: ctx.insertionPoint!)

    case .byValue:
      let x = ctx.value[ctx.ir.returnRegister!]!
      let y = ctx.module.llvm.insertLoad(p.type.llvm, from: x, at: ctx.insertionPoint!)
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
    let m = ctx.llvm.declareFunction("main", ctx.llvm.functionType(from: [], to: i32.t))
    let e = ctx.llvm.appendBlock(to: m)
    let p = ctx.llvm.endOf(e)
    let r = ctx.llvm.insertCall(f.value, on: [], at: p)

    // `f` returns an exit status iff its return type has a non-zero size, in which case we can
    // assume it is an instance of `Hylo.Int32`.
    if f.prototype.mapping.output!.type.layout.size != 0 {
      let v = ctx.llvm.insertExtractValue(from: r, at: 0, at: p)
      ctx.llvm.insertReturn(v, at: p)
    } else {
      ctx.llvm.insertReturn(i32.unsafe[].zero, at: p)
    }
  }

  /// Returns the representation of `v` in LLVM IR.
  private mutating func codegen(
    _ v: FrontEnd.IRValue, in ctx: inout FunctionGenerationContext
  ) -> LLVMValue {
    switch v {
    case .parameter, .register:
      return ctx.value[v]!
    case .integer(let n, let t):
      return codegen(integer: n, instanceOf: t, in: &ctx.module)
    case .function(let n, _):
      return demandFunction(named: n, in: &ctx.module).value.v
    default:
      fatalError("no LLVM representation of the Hylo value '\(show(v))'")
    }
  }

  /// Returns a LLVM IR constant equivalent to `n`, which is an instance of an integer type `t`.
  private mutating func codegen(
    integer n: BigInt, instanceOf t: MachineType.ID, in ctx: inout ModuleGenerationContext
  ) -> LLVMValue {
    let u = metadata(of: t, in: &ctx)
    let t = IntegerType.UnsafeReference(u.llvm)!
    if n == 0 {
      return t.unsafe[].zero.v
    } else {
      return t.unsafe[].constant(words: n.words.map(UInt64.init(_:))).v
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
    case Arrow.self:
      metadata(of: types.castUnchecked(t, to: Arrow.self), in: &ctx)
    case Enum.self:
      metadata(of: types.castUnchecked(t, to: Enum.self), in: &ctx)
    case GenericParameter.self:
      metadata(of: types.castUnchecked(t, to: GenericParameter.self), in: &ctx)
    case MachineType.self:
      metadata(of: types.castUnchecked(t, to: MachineType.self), in: &ctx)
    case Struct.self:
      metadata(of: types.castUnchecked(t, to: Struct.self), in: &ctx)
    case Tuple.self:
      metadata(of: types.castUnchecked(t, to: Tuple.self), in: &ctx)
    case TypeApplication.self:
      metadata(of: types.castUnchecked(t, to: TypeApplication.self), in: &ctx)
    case TypeWitness.self:
      metadata(of: types.castUnchecked(t, to: TypeWitness.self), in: &ctx)
    default:
      unimplemented("no LLVM representation of the type '\(show(t))'")
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Arrow.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      let v = ctx.llvm.functionPointer.t
      let s = ctx.llvm.layout.storageSize(of: v)
      let a = ctx.llvm.layout.preferredAlignment(of: v)
      let l = ConcreteLayout(fields: [], propertyToField: [], size: .fixed(s), alignment: a)
      return TypeMetadata(llvm: v, layout: l)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Enum.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    // Is there a raw representation?
    if self[types[t].declaration].representation != nil {
      unimplemented("enum raw representation")
    }

    return metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      program.metadata(
        enum: n, cases: program.storage(of: t.erased, visibleFrom: ctx.hylo)!, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: GenericParameter.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    let v = ctx.llvm.ptr.t
    let a = ctx.llvm.layout.preferredAlignment(of: v)
    let l = ConcreteLayout(fields: [], propertyToField: [], size: .dynamic, alignment: a)
    return .init(llvm: v, layout: l)
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: MachineType.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      let v = switch program.types[t] {
      case .i(let width):
        ctx.llvm.integerType(Int(width)).t
      case .word:
        ctx.llvm.iptr.t
      case .ptr:
        ctx.llvm.ptr.t
      default:
        unimplemented("no LLVM representation of the type '\(program.show(t))'")
      }

      let s = ctx.llvm.layout.storageSize(of: v)
      let a = ctx.llvm.layout.preferredAlignment(of: v)
      let l = ConcreteLayout(fields: [], propertyToField: [], size: .fixed(s), alignment: a)
      return TypeMetadata(llvm: v, layout: l)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Struct.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      // TODO: Resilience
      let properties = program.fields(of: t.erased, visibleFrom: ctx.hylo)!
      return program.metadata(record: n, fields: properties, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: Tuple.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      let (properties, isOpenEnded) = program.types.members(of: t)
      precondition(!isOpenEnded, "no LLVM representation of type '\(program.show(t))'")
      return program.metadata(record: n, fields: properties, in: &ctx)
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: TypeApplication.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    metadata(of: t, in: &ctx) { (program, ctx, t, n) in
      if let (concept, _) = program.types.seenAsTraitApplication(t) {
        // Implementations of associated types and nested conformances are stored as object
        // pointers. Other implementations are stored as function pointers.
        let rs = program.requirements(of: concept)
        var fs: [LLVMType] = .init(minimumCapacity: rs.all.count)
        fs.append(ctx.llvm.ptr.t, count: rs.all.count - rs.members.count)
        fs.append(ctx.llvm.functionPointer.t, count: rs.members.count)

        let v = ctx.llvm.structType(named: n, fs)
        let s = ctx.llvm.layout.storageSize(of: v)
        let a = ctx.llvm.layout.preferredAlignment(of: v)
        let l = ConcreteLayout(
          fields: [], propertyToField: Array(fs.indices), size: .fixed(s), alignment: a)
        return TypeMetadata(llvm: v, layout: l)
      } else {
        fatalError("no LLVM metadata representation of the type '\(program.show(t))'")
      }
    }
  }

  /// Returns the LLVM type representation of the Hylo type `t`.
  private mutating func metadata(
    of t: TypeWitness.ID, in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    let p = types.demand(MachineType.ptr)
    return metadata(of: p, in: &ctx)
  }

  /// Returns the LLVM type representation of a record type having the given name and fields.
  private mutating func metadata(
    record name: String, fields: [AnyTypeIdentity], in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    let layout = record(fields: fields, in: &ctx)
    let definition = ctx.llvm.structType(named: name, layout.fields, packed: true)

    assert(ctx.llvm.layout.storageSize(of: definition) <= layout.size.fixed!)
    assert(ctx.llvm.layout.abiAlignment(of: definition) <= layout.alignment)
    return TypeMetadata(llvm: definition, layout: layout)
  }

  /// Returns the LLVM type representation of a sum type having the given name and cases.
  private mutating func metadata(
    enum name: String, cases: [AnyTypeIdentity], in ctx: inout ModuleGenerationContext
  ) -> TypeMetadata {
    // Trivial if there are less than two cases.
    if cases.count <= 1 {
      return metadata(record: name, fields: Array(contentsOf: cases.uniqueElement), in: &ctx)
    }

    // Otherwise, construct a pair leading with the tag.
    else {
      var payloadSize = 0
      var payloadAlignment = 1
      for c in cases {
        let m = metadata(of: c, in: &ctx)
        payloadSize = max(payloadSize, m.layout.size.fixed!)
        payloadAlignment = max(payloadAlignment, m.layout.alignment)
      }

      // Pad the size of the tag to satisfy the alignment of the payload.
      let tag = ctx.integerTypeToRepresent(cases.count)
      let tagSize = ctx.llvm.layout.storageSize(of: tag).rounded(
        upToNearestMultipleOf: payloadAlignment)

      let fields: [LLVMType] = [
        ctx.llvm.arrayType(tagSize, ctx.llvm.i8).t,
        ctx.llvm.arrayType(payloadSize, ctx.llvm.i8).t
      ]

      let pair = ctx.llvm.structType(named: name, fields, packed: true)
      let layout = ConcreteLayout(
        fields: fields, propertyToField: [0, 1],
        size: .fixed(tagSize + payloadSize),
        alignment: max(payloadAlignment, ctx.llvm.layout.preferredAlignment(of: tag)))
      return .init(llvm: pair, layout: layout)
    }
  }

  /// Returns the standard layout of a record type having the given fields.
  private mutating func record(
    fields: [AnyTypeIdentity], in ctx: inout ModuleGenerationContext
  ) -> ConcreteLayout {
    let rs = fields.map({ (u) in metadata(of: u, in: &ctx) })
    let ps = fields.indices.sorted { (a, b) in
      let lhs = rs[a].layout.alignment
      let rhs = rs[b].layout.alignment
      return (rhs < lhs) || ((lhs == rhs) && (a < b))
    }

    var elements: [LLVMType] = []
    var fieldToElement = Array(repeating: -1, count: rs.count)
    var size = 0

    for p in ps {
      let fieldSize = rs[p].layout.size.fixed ?? fatalError("unexpected dynamic size")
      if fieldSize == 0 { continue }

      // Compute the offset of the next property.
      let next = size.rounded(upToNearestMultipleOf: rs[p].layout.alignment)

      // Add padding if necessary.
      if next != size {
        let padding = next - size
        elements.append(ctx.llvm.arrayType(padding, ctx.llvm.i8).t)
      }

      fieldToElement[p] = elements.count
      elements.append(rs[p].llvm)
      size = next + fieldSize
    }

    let a = rs.last?.layout.alignment ?? 1
    return ConcreteLayout(
      fields: elements, propertyToField: fieldToElement, size: .fixed(size), alignment: a)
  }

  /// Returns the LLVM IR type of the entity declared by `d`, which is a property of an opaque
  /// record having type `t`.
  private mutating func typeOfProperty(
    declaredBy d: DeclarationIdentity, withType t: AnyTypeIdentity,
    in ctx: inout ModuleGenerationContext
  ) -> LLVMType {
    if isFunctionOrVariantDeclaration(d) {
      return ctx.llvm.functionPointer.t
    } else {
      return metadata(of: t, in: &ctx).llvm
    }
  }

  /// Returns `v` iff identifies a subscript known to have a slide that compiles to a no-op.
  private func seenAsAddressor(
    _ v: FrontEnd.IRValue, in ctx: borrowing FunctionGenerationContext
  ) -> IRFunction.Name? {
    switch v {
    case .function(let f, _):
      if case .remote(_, _, let b) = self[ctx.module.hylo].ir.functions[f]?.output {
        return b ? f : nil
      } else {
        return nil
      }

    default:
      return nil
    }
  }

}

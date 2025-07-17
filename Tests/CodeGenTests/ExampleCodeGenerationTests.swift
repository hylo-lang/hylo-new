// Copied from SwiftyLLVM test suite.
import SwiftyLLVM
import XCTest

final class CodeGenerationTests: XCTestCase {

  func testO0() throws {
    var m = Module("math")
    m.emitTest()
    m.runDefaultModulePasses(optimization: .none)
    XCTAssertNoThrow(try m.verify())
  }

  func testO1() throws {
    var m = Module("math")
    m.emitTest()
    m.runDefaultModulePasses(optimization: .less)
    XCTAssertNoThrow(try m.verify())
  }

  func testO2() throws {
    var m = Module("math")
    m.emitTest()
    m.runDefaultModulePasses(optimization: .default)
    XCTAssertNoThrow(try m.verify())
  }

  func testO3() throws {
    var m = Module("math")
    m.emitTest()
    m.runDefaultModulePasses(optimization: .aggressive)
    XCTAssertNoThrow(try m.verify())
  }

}

extension Module {

  /// Emits contents in `self` to prepare the tests in `CodeGenerationTests`.
  ///
  /// Two functions are emitted, implementing a program equivalent to the one below, which is
  /// written in Hylo:
  ///
  ///     subscript degrees(_ radians: inout Float64): Float64 {
  ///       inout {
  ///         var d = radians * 180.0 / Float64.pi()
  ///         yield &d
  ///         &radians = d * Float64.pi() / 180.0
  ///       }
  ///     }
  ///
  ///     public fun main() -> Int32 {
  ///       var r = Float64.pi()
  ///       &degrees[&r] -= 180.0
  ///       return if r == 0 { 0 } else { 1 }
  ///     }
  ///
  /// `self` is expected to be empty.
  ///
  /// In addition to these functions, we also emit a function that test atomics operations.
  fileprivate mutating func emitTest() {
    let r2d = emitProjectDegrees()
    _ = emitMain(projectingDegreesWith: r2d)
    _ = emitTestAtomics()
  }

  /// Defines a function `main` that calls the coroutine created by `emitProjectDegrees`.
  private mutating func emitMain(
    projectingDegreesWith projectDegrees: Function
  ) -> Function {
    let s = FunctionType(from: [], to: i32, in: &self)
    let f = declareFunction("main", s)

    let b0 = appendBlock(named: "b0", to: f)

    // %0 = alloca [16 x i8], align 8
    // %1 = alloca double, align 8
    let x0 = insertAlloca(ArrayType(16, i8, in: &self), at: endOf(b0))
    setAlignment(8, for: x0)
    let x1 = insertAlloca(double, at: endOf(b0))

    // store double 0x400921FB54442D18, ptr %1, align 8
    insertStore(double(.pi), to: x1, at: endOf(b0))

    // %2 = call ptr @llvm.coro.prepare.retcon(ptr @deg)
    // %3 = call { ptr, ptr } %2(ptr %0, ptr %1)
    let prepare = intrinsic(named: Intrinsic.llvm.coro.prepare.retcon)!
    let x2 = insertCall(Function(prepare)!, on: [projectDegrees], at: endOf(b0))
    let x3 = insertCall(x2, typed: projectDegrees.valueType, on: [x0, x1], at: endOf(b0))

    // %4 = extractvalue { ptr, ptr } %3, 1
    // %5 = load double, ptr %4, align 8
    // %6 = fsub double %5, 1.800000e+02
    // store double %6, ptr %4, align 8
    let x4 = insertExtractValue(from: x3, at: 1, at: endOf(b0))
    let x5 = insertLoad(double, from: x4, at: endOf(b0))
    let x6 = insertFSub(x5, double(180), at: endOf(b0))
    insertStore(x6, to: x4, at: endOf(b0))

    // %7 = extractvalue { ptr, ptr } %3, 0
    // call void %7(ptr %0, i1 false
    let x7 = insertExtractValue(from: x3, at: 0, at: endOf(b0))
    _ = insertCall(
      x7, typed: FunctionType(from: [ptr, i1], in: &self), on: [x0, i1(0)], at: endOf(b0))

    // %8 = load double, ptr %1, align 8
    // %9 = fcmp ueq double %8, 0.000000e+00
    // %10 = zext i1 %9 to i32
    let x8 = insertLoad(double, from: x1, at: endOf(b0))
    let x9 = insertFloatingPointComparison(.ueq, x8, double(0), at: endOf(b0))
    let xa = insertZeroExtend(x9, to: i32, at: endOf(b0))

    // ret i32 %10
    insertReturn(xa, at: endOf(b0))

    return f
  }

  /// Defines a coroutine that projects the value in degrees of an angle passed in radians.
  private mutating func emitProjectDegrees() -> Function {
    // declare void @slide(ptr, i1 zeroext)
    let slide = declareFunction("slide", .init(from: [ptr, i1], in: &self))
    addAttribute(.init(.zeroext, in: &self), to: slide.parameters[1])

    // declare noalias ptr @alloc(i32)
    let alloc = declareFunction("alloc", .init(from: [i32], to: ptr, in: &self))
    addAttribute(.init(.noalias, in: &self), to: alloc.returnValue)

    // declare void @dealloc(ptr)
    let dealloc = declareFunction("dealloc", .init(from: [ptr], in: &self))

    // define { ptr, ptr } @deg(ptr %0, ptr %1)
    let s = FunctionType(from: [ptr, ptr], to: StructType([ptr, ptr], in: &self), in: &self)
    let f = declareFunction("deg", s)
    let r = f.parameters.last!

    let b0 = appendBlock(named: "b0", to: f)

    // %2 = alloca double, align 8
    let x0 = insertAlloca(double, at: endOf(b0))

    // %3 = call token @llvm.coro.id.retcon.once(
    //   i32 16, i32 8, ptr %0, ptr @slide, ptr @alloc, ptr @dealloc)
    let retconOnce = intrinsic(named: Intrinsic.llvm.coro.id.retcon.once)!
    let coroutineID = insertCall(
      Function(retconOnce)!,
      on: [
        i32(16),  // size of the frame buffer
        i32(8),  // alignment of the frame buffer
        f.parameters.first!,  // the frame buffer
        slide, alloc, dealloc
      ],
      at: endOf(b0))

    // %4 = call ptr @llvm.coro.begin(token %3, ptr null)
    let begin = intrinsic(named: Intrinsic.llvm.coro.begin)!
    let coroutineHandle = insertCall(
      Function(begin)!,
      on: [coroutineID, ptr.null],
      at: endOf(b0))

    // %5 = load double, ptr %1, align 8
    // %6 = fmul double %5, 1.800000e+02
    // %7 = fdiv double %6, 0x400921FB54442D18
    // store double %7, ptr %2, align 8
    let x1 = insertLoad(double, from: r, at: endOf(b0))
    let x2 = insertFMul(x1, double(180), at: endOf(b0))
    let x3 = insertFDiv(x2, double(.pi), at: endOf(b0))
    insertStore(x3, to: x0, at: endOf(b0))

    // %8 = call i1 (...) @llvm.coro.suspend.retcon.i1(ptr %2)
    let suspend = intrinsic(named: Intrinsic.llvm.coro.suspend.retcon, for: [i1])!
    _ = insertCall(Function(suspend)!, on: [x0], at: endOf(b0))

    // %9 = load double, ptr %2, align 8
    // %10 = fmul double %9, 0x400921FB54442D18
    // %11 = fdiv double %10, 1.800000e+02
    // store double %11, ptr %1, align 8
    let x4 = insertLoad(double, from: x0, at: endOf(b0))
    let x5 = insertFMul(x4, double(.pi), at: endOf(b0))
    let x6 = insertFDiv(x5, double(180), at: endOf(b0))
    insertStore(x6, to: r, at: endOf(b0))

    // %12 = call token @llvm.coro.end.results()
    let results = intrinsic(named: Intrinsic.llvm.coro.end.results)!
    let resultToken = insertCall(Function(results)!, on: [], at: endOf(b0))
    
    // %13 = call i1 @llvm.coro.end(ptr %4, i1 false, token %12)
    let end = intrinsic(named: Intrinsic.llvm.coro.end)!
    _ = insertCall(Function(end)!, on: [coroutineHandle, i1(0), resultToken], at: endOf(b0))

    // unreachable
    insertUnreachable(at: endOf(b0))

    return f
  }

  private mutating func emitTestAtomics() -> Function {
    let s = FunctionType(from: [], in: &self)
    let f = declareFunction("testAtomics", s)

    let b0 = appendBlock(named: "b0", to: f)

    // %0 = alloca i64, align 8
    // %1 = alloca double, align 8
    let x0 = insertAlloca(i64, at: endOf(b0))
    let x1 = insertAlloca(double, at: endOf(b0))

    // store atomic double 0x400921FB54442D18, ptr %1 monotonic, align 8
    // store atomic double 0x400921FB54442D18, ptr %1 release, align 8
    // store atomic double 0x400921FB54442D18, ptr %1 seq_cst, align 8
    let s1 = insertStore(double(.pi), to: x1, at: endOf(b0))
    setOrdering(.monotonic, for: s1)
    let s2 = insertStore(double(.pi), to: x1, at: endOf(b0))
    setOrdering(.release, for: s2)
    let s3 = insertStore(double(.pi), to: x1, at: endOf(b0))
    setOrdering(.sequentiallyConsistent, for: s3)

    // %2 = load atomic double, ptr %1 monotonic, align 8
    // %3 = load atomic double, ptr %1 acquire, align 8
    // %4 = load atomic double, ptr %1 seq_cst, align 8
    let x2 = insertLoad(double, from: x1, at: endOf(b0))
    setOrdering(.monotonic, for: x2)
    let x3 = insertLoad(double, from: x1, at: endOf(b0))
    setOrdering(.acquire, for: x3)
    let x4 = insertLoad(double, from: x1, at: endOf(b0))
    setOrdering(.sequentiallyConsistent, for: x4)

    // %5 = atomicrmw xchg ptr %1, double 0x400921FB54442D18 monotonic, align 8
    // %6 = atomicrmw xchg ptr %1, double 0x400921FB54442D18 acquire, align 8
    // %7 = atomicrmw xchg ptr %1, double 0x400921FB54442D18 release, align 8
    // %8 = atomicrmw xchg ptr %1, double 0x400921FB54442D18 acq_rel, align 8
    // %9 = atomicrmw xchg ptr %1, double 0x400921FB54442D18 seq_cst, align 8
    let _ = insertAtomicRMW(x1, operation: .xchg, value: double(.pi), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .xchg, value: double(.pi), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .xchg, value: double(.pi), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .xchg, value: double(.pi), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .xchg, value: double(.pi), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %10 = atomicrmw add ptr %0, i64 11 monotonic, align 8
    // %11 = atomicrmw add ptr %0, i64 11 acquire, align 8
    // %12 = atomicrmw add ptr %0, i64 11 release, align 8
    // %13 = atomicrmw add ptr %0, i64 11 acq_rel, align 8
    // %14 = atomicrmw add ptr %0, i64 11 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .add, value: i64(11), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .add, value: i64(11), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .add, value: i64(11), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .add, value: i64(11), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .add, value: i64(11), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %15 = atomicrmw fadd ptr %1, double 0x400921FB54442D18 monotonic, align 8
    // %16 = atomicrmw fadd ptr %1, double 0x400921FB54442D18 acquire, align 8
    // %17 = atomicrmw fadd ptr %1, double 0x400921FB54442D18 release, align 8
    // %18 = atomicrmw fadd ptr %1, double 0x400921FB54442D18 acq_rel, align 8
    // %19 = atomicrmw fadd ptr %1, double 0x400921FB54442D18 seq_cst, align 8
    let _ = insertAtomicRMW(x1, operation: .fAdd, value: double(.pi), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fAdd, value: double(.pi), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fAdd, value: double(.pi), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fAdd, value: double(.pi), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fAdd, value: double(.pi), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %20 = atomicrmw sub ptr %0, i64 13 monotonic, align 8
    // %21 = atomicrmw sub ptr %0, i64 13 acquire, align 8
    // %22 = atomicrmw sub ptr %0, i64 13 release, align 8
    // %23 = atomicrmw sub ptr %0, i64 13 acq_rel, align 8
    // %24 = atomicrmw sub ptr %0, i64 13 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .sub, value: i64(13), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .sub, value: i64(13), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .sub, value: i64(13), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .sub, value: i64(13), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .sub, value: i64(13), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %25 = atomicrmw fsub ptr %1, double 0x400921FB54442D18 monotonic, align 8
    // %26 = atomicrmw fsub ptr %1, double 0x400921FB54442D18 acquire, align 8
    // %27 = atomicrmw fsub ptr %1, double 0x400921FB54442D18 release, align 8
    // %28 = atomicrmw fsub ptr %1, double 0x400921FB54442D18 acq_rel, align 8
    // %29 = atomicrmw fsub ptr %1, double 0x400921FB54442D18 seq_cst, align 8
    let _ = insertAtomicRMW(x1, operation: .fSub, value: double(.pi), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fSub, value: double(.pi), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fSub, value: double(.pi), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fSub, value: double(.pi), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fSub, value: double(.pi), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %30 = atomicrmw max ptr %0, i64 17 monotonic, align 8
    // %31 = atomicrmw max ptr %0, i64 17 acquire, align 8
    // %32 = atomicrmw max ptr %0, i64 17 release, align 8
    // %33 = atomicrmw max ptr %0, i64 17 acq_rel, align 8
    // %34 = atomicrmw max ptr %0, i64 17 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .max, value: i64(17), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .max, value: i64(17), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .max, value: i64(17), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .max, value: i64(17), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .max, value: i64(17), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %35 = atomicrmw umax ptr %0, i64 19 monotonic, align 8
    // %36 = atomicrmw umax ptr %0, i64 19 acquire, align 8
    // %37 = atomicrmw umax ptr %0, i64 19 release, align 8
    // %38 = atomicrmw umax ptr %0, i64 19 acq_rel, align 8
    // %39 = atomicrmw umax ptr %0, i64 19 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .uMax, value: i64(19), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMax, value: i64(19), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMax, value: i64(19), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMax, value: i64(19), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMax, value: i64(19), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %40 = atomicrmw fmax ptr %1, double 0x400921FB54442D18 monotonic, align 8
    // %41 = atomicrmw fmax ptr %1, double 0x400921FB54442D18 acquire, align 8
    // %42 = atomicrmw fmax ptr %1, double 0x400921FB54442D18 release, align 8
    // %43 = atomicrmw fmax ptr %1, double 0x400921FB54442D18 acq_rel, align 8
    // %44 = atomicrmw fmax ptr %1, double 0x400921FB54442D18 seq_cst, align 8
    let _ = insertAtomicRMW(x1, operation: .fMax, value: double(.pi), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMax, value: double(.pi), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMax, value: double(.pi), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMax, value: double(.pi), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMax, value: double(.pi), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %45 = atomicrmw min ptr %0, i64 17 monotonic, align 8
    // %46 = atomicrmw min ptr %0, i64 17 acquire, align 8
    // %47 = atomicrmw min ptr %0, i64 17 release, align 8
    // %48 = atomicrmw min ptr %0, i64 17 acq_rel, align 8
    // %49 = atomicrmw min ptr %0, i64 17 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .min, value: i64(17), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .min, value: i64(17), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .min, value: i64(17), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .min, value: i64(17), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .min, value: i64(17), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %50 = atomicrmw umin ptr %0, i64 19 monotonic, align 8
    // %51 = atomicrmw umin ptr %0, i64 19 acquire, align 8
    // %52 = atomicrmw umin ptr %0, i64 19 release, align 8
    // %53 = atomicrmw umin ptr %0, i64 19 acq_rel, align 8
    // %54 = atomicrmw umin ptr %0, i64 19 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .uMin, value: i64(19), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMin, value: i64(19), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMin, value: i64(19), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMin, value: i64(19), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .uMin, value: i64(19), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %55 = atomicrmw fmin ptr %1, double 0x400921FB54442D18 monotonic, align 8
    // %56 = atomicrmw fmin ptr %1, double 0x400921FB54442D18 acquire, align 8
    // %57 = atomicrmw fmin ptr %1, double 0x400921FB54442D18 release, align 8
    // %58 = atomicrmw fmin ptr %1, double 0x400921FB54442D18 acq_rel, align 8
    // %59 = atomicrmw fmin ptr %1, double 0x400921FB54442D18 seq_cst, align 8
    let _ = insertAtomicRMW(x1, operation: .fMin, value: double(.pi), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMin, value: double(.pi), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMin, value: double(.pi), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMin, value: double(.pi), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x1, operation: .fMin, value: double(.pi), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %60 = atomicrmw and ptr %0, i64 23 monotonic, align 8
    // %61 = atomicrmw and ptr %0, i64 23 acquire, align 8
    // %62 = atomicrmw and ptr %0, i64 23 release, align 8
    // %63 = atomicrmw and ptr %0, i64 23 acq_rel, align 8
    // %64 = atomicrmw and ptr %0, i64 23 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .and, value: i64(23), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .and, value: i64(23), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .and, value: i64(23), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .and, value: i64(23), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .and, value: i64(23), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %65 = atomicrmw nand ptr %0, i64 29 monotonic, align 8
    // %66 = atomicrmw nand ptr %0, i64 29 acquire, align 8
    // %67 = atomicrmw nand ptr %0, i64 29 release, align 8
    // %68 = atomicrmw nand ptr %0, i64 29 acq_rel, align 8
    // %69 = atomicrmw nand ptr %0, i64 29 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .nand, value: i64(29), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .nand, value: i64(29), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .nand, value: i64(29), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .nand, value: i64(29), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .nand, value: i64(29), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %70 = atomicrmw or ptr %0, i64 31 monotonic, align 8
    // %71 = atomicrmw or ptr %0, i64 31 acquire, align 8
    // %72 = atomicrmw or ptr %0, i64 31 release, align 8
    // %73 = atomicrmw or ptr %0, i64 31 acq_rel, align 8
    // %74 = atomicrmw or ptr %0, i64 31 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .or, value: i64(31), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .or, value: i64(31), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .or, value: i64(31), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .or, value: i64(31), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .or, value: i64(31), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %75 = atomicrmw xor ptr %0, i64 37 monotonic, align 8
    // %76 = atomicrmw xor ptr %0, i64 37 acquire, align 8
    // %77 = atomicrmw xor ptr %0, i64 37 release, align 8
    // %78 = atomicrmw xor ptr %0, i64 37 acq_rel, align 8
    // %79 = atomicrmw xor ptr %0, i64 37 seq_cst, align 8
    let _ = insertAtomicRMW(x0, operation: .xor, value: i64(37), ordering: .monotonic, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .xor, value: i64(37), ordering: .acquire, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .xor, value: i64(37), ordering: .release, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .xor, value: i64(37), ordering: .acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertAtomicRMW(x0, operation: .xor, value: i64(37), ordering: .sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // %80 = cmpxchg ptr %0, i64 41, i64 43 monotonic monotonic, align 8
    // %81 = cmpxchg ptr %0, i64 41, i64 43 monotonic acquire, align 8
    // %82 = cmpxchg ptr %0, i64 41, i64 43 monotonic seq_cst, align 8
    // %83 = cmpxchg ptr %0, i64 41, i64 43 acquire monotonic, align 8
    // %84 = cmpxchg ptr %0, i64 41, i64 43 acquire acquire, align 8
    // %85 = cmpxchg ptr %0, i64 41, i64 43 acquire seq_cst, align 8
    // %86 = cmpxchg ptr %0, i64 41, i64 43 release monotonic, align 8
    // %87 = cmpxchg ptr %0, i64 41, i64 43 release acquire, align 8
    // %88 = cmpxchg ptr %0, i64 41, i64 43 release seq_cst, align 8
    // %89 = cmpxchg ptr %0, i64 41, i64 43 acq_rel monotonic, align 8
    // %90 = cmpxchg ptr %0, i64 41, i64 43 acq_rel acquire, align 8
    // %91 = cmpxchg ptr %0, i64 41, i64 43 acq_rel seq_cst, align 8
    // %92 = cmpxchg ptr %0, i64 41, i64 43 seq_cst monotonic, align 8
    // %93 = cmpxchg ptr %0, i64 41, i64 43 seq_cst acquire, align 8
    // %94 = cmpxchg ptr %0, i64 41, i64 43 seq_cst seq_cst, align 8
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .monotonic, failureOrdering: .monotonic, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .monotonic, failureOrdering: .acquire, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .monotonic, failureOrdering: .sequentiallyConsistent, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquire, failureOrdering: .monotonic, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquire, failureOrdering: .acquire, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquire, failureOrdering: .sequentiallyConsistent, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .release, failureOrdering: .monotonic, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .release, failureOrdering: .acquire, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .release, failureOrdering: .sequentiallyConsistent, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquireRelease, failureOrdering: .monotonic, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquireRelease, failureOrdering: .acquire, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquireRelease, failureOrdering: .sequentiallyConsistent, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .sequentiallyConsistent, failureOrdering: .monotonic, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .sequentiallyConsistent, failureOrdering: .acquire, weak: false, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .sequentiallyConsistent, failureOrdering: .sequentiallyConsistent, weak: false, singleThread: false, at: endOf(b0))

    // %95 = cmpxchg weak ptr %0, i64 41, i64 43 monotonic monotonic, align 8
    // %96 = cmpxchg weak ptr %0, i64 41, i64 43 monotonic acquire, align 8
    // %97 = cmpxchg weak ptr %0, i64 41, i64 43 monotonic seq_cst, align 8
    // %98 = cmpxchg weak ptr %0, i64 41, i64 43 acquire monotonic, align 8
    // %99 = cmpxchg weak ptr %0, i64 41, i64 43 acquire acquire, align 8
    // %100 = cmpxchg weak ptr %0, i64 41, i64 43 acquire seq_cst, align 8
    // %101 = cmpxchg weak ptr %0, i64 41, i64 43 release monotonic, align 8
    // %102 = cmpxchg weak ptr %0, i64 41, i64 43 release acquire, align 8
    // %103 = cmpxchg weak ptr %0, i64 41, i64 43 release seq_cst, align 8
    // %104 = cmpxchg weak ptr %0, i64 41, i64 43 acq_rel monotonic, align 8
    // %105 = cmpxchg weak ptr %0, i64 41, i64 43 acq_rel acquire, align 8
    // %106 = cmpxchg weak ptr %0, i64 41, i64 43 acq_rel seq_cst, align 8
    // %107 = cmpxchg weak ptr %0, i64 41, i64 43 seq_cst monotonic, align 8
    // %108 = cmpxchg weak ptr %0, i64 41, i64 43 seq_cst acquire, align 8
    // %109 = cmpxchg weak ptr %0, i64 41, i64 43 seq_cst seq_cst, align 8
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .monotonic, failureOrdering: .monotonic, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .monotonic, failureOrdering: .acquire, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .monotonic, failureOrdering: .sequentiallyConsistent, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquire, failureOrdering: .monotonic, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquire, failureOrdering: .acquire, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquire, failureOrdering: .sequentiallyConsistent, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .release, failureOrdering: .monotonic, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .release, failureOrdering: .acquire, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .release, failureOrdering: .sequentiallyConsistent, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquireRelease, failureOrdering: .monotonic, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquireRelease, failureOrdering: .acquire, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .acquireRelease, failureOrdering: .sequentiallyConsistent, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .sequentiallyConsistent, failureOrdering: .monotonic, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .sequentiallyConsistent, failureOrdering: .acquire, weak: true, singleThread: false, at: endOf(b0))
    let _ = insertAtomicCmpXchg(x0, old: i64(41), new: i64(43), successOrdering: .sequentiallyConsistent, failureOrdering: .sequentiallyConsistent, weak: true, singleThread: false, at: endOf(b0))

    // fence acquire
    // fence release
    // fence acq_rel
    // fence seq_cst
    let _ = insertFence(.acquire, singleThread: false, at: endOf(b0))
    let _ = insertFence(.release, singleThread: false, at: endOf(b0))
    let _ = insertFence(.acquireRelease, singleThread: false, at: endOf(b0))
    let _ = insertFence(.sequentiallyConsistent, singleThread: false, at: endOf(b0))

    // fence syncscope("singlethread") acquire
    // fence syncscope("singlethread") release
    // fence syncscope("singlethread") acq_rel
    // fence syncscope("singlethread") seq_cst
    let _ = insertFence(.acquire, singleThread: true, at: endOf(b0))
    let _ = insertFence(.release, singleThread: true, at: endOf(b0))
    let _ = insertFence(.acquireRelease, singleThread: true, at: endOf(b0))
    let _ = insertFence(.sequentiallyConsistent, singleThread: true, at: endOf(b0))

    // ret void
    insertReturn(at: endOf(b0))

    return f
  }

}
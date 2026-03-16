import FrontEnd
import SwiftyLLVM
import Utilities

extension Program {
  func llvmType<T: TypeIdentity>(from t: T, in module: inout SwiftyLLVM.Module)
    -> SwiftyLLVM.AnyType.UnsafeReference
  {
    switch types.tag(of: t) {
    case Arrow.self:
      return llvmType(from: types.castUnchecked(t, to: Arrow.self), in: &module)
    case Enum.self:
      unimplemented("LLVM type lowering for enum types")
    case FunctionPointer.self:
      return llvmType(fromFunctionPointer: types.castUnchecked(t, to: FunctionPointer.self), in: &module).erased
    case MachineType.self:
      return llvmType(fromMachineType: types.castUnchecked(t, to: MachineType.self), in: &module).erased
    case RemoteType.self:
      return module.ptr.erased
    case Struct.self:
      return llvmType(fromStruct: types.castUnchecked(t, to: Struct.self), in: &module).erased
    case Tuple.self:
      return llvmType(fromTuple: types.castUnchecked(t, to: Tuple.self), in: &module).erased
    default:
      unimplemented("LLVM type lowering for type \(show(t))")
    }
  }

  /// Returns the LLVM type representation of an Arrow type.
  func llvmType(from arrow: ConcreteTypeIdentity<Arrow>, in module: inout SwiftyLLVM.Module)
    -> SwiftyLLVM.StructType.UnsafeReference
  {
    let environment = llvmType(from: types[arrow].environment, in: &module)
    return module.structType((module.ptr, environment))
  }

  /// Returns the LLVM type representation of a function pointer type.
  func llvmType(
    fromFunctionPointer f: ConcreteTypeIdentity<FunctionPointer>, in module: inout SwiftyLLVM.Module
  )
    -> SwiftyLLVM.PointerType.UnsafeReference
  {
    return module.functionPointer
  }

  /// Returns the LLVM type representation of a builtin type.
  func llvmType(fromMachineType machineType: ConcreteTypeIdentity<MachineType>, in module: inout SwiftyLLVM.Module)
    -> SwiftyLLVM.AnyType.UnsafeReference
  {
    switch types[machineType] {
    case .i(let bitWidth):
      return module.integerType(Int(bitWidth)).erased
    case .word:
      return module.layout.pointerSizedIntegerType.erased
    case .float16:
      return module.half.erased
    case .float32:
      return module.float.erased
    case .float64:
      return module.double.erased
    case .float128:
      return module.fp128.erased
    case .ptr:
      return module.ptr.erased
    }
  }

  func llvmType(fromTuple tuple: ConcreteTypeIdentity<Tuple>, in module: inout SwiftyLLVM.Module)
    -> SwiftyLLVM.StructType.UnsafeReference
  {
    module.structType(
      types.members(of: tuple).types.map { llvmType(from: $0, in: &module) },
      packed: false  // TODO: use our own layout algorithm, manually emitting padding bits.
    )
  }

  func llvmType(fromStruct structType: ConcreteTypeIdentity<Struct>, in module: inout SwiftyLLVM.Module)
    -> SwiftyLLVM.StructType.UnsafeReference
  {
    module.structType(
      named: llvmName(of: structType.erased),
      storedPropertyTypes(of: structType).map { llvmType(from: $0, in: &module) },
      packed: false  // TODO: use our own layout algorithm, manually emitting padding bits.
    )
  }

  func storedPropertyTypes(of structType: ConcreteTypeIdentity<Struct>) -> [AnyTypeIdentity] {
    storedProperties(of: types[structType].declaration).map { variableDeclaration in
      type(assignedTo: variableDeclaration)
    }
  }

}

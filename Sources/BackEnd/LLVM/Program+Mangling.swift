import FrontEnd
import Utilities

extension Program {
  func llvmName(of type: AnyTypeIdentity) -> String {
    switch types.tag(of: type) {
    case Struct.self:
      let s = types[types.castUnchecked(type, to: Struct.self)]
      return self[s.declaration].identifier.value
    default:
      unimplemented("mangling for type \(show(type))")
    }
  }

  func llvmName(of f: IRFunction) -> String {
    return llvmName(of: f.name)
  }

  func llvmName(of f: IRFunction.Name) -> String {
    var p = TreePrinter(program: self) // todo
    return "hylo_" + f.show(using: &p)
  }
}

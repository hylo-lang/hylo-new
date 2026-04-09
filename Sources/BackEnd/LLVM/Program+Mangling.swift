import FrontEnd
import Utilities

extension Program {
  /// Returns the mangled name of the type `type`.
  func llvmName(of type: AnyTypeIdentity) -> String {
    // FIXME: use actual mangling.
    switch types.tag(of: type) {
    case Struct.self:
      let s = types[types.castUnchecked(type, to: Struct.self)]
      return self[s.declaration].identifier.value
    default:
      unimplemented("mangling for type \(show(type))")
    }
  }

  /// Returns the mangled name of function `f`.
  func llvmName(of f: IRFunction) -> String {
    // FIXME: use actual mangling.
    return llvmName(of: f.name)
  }

  /// Returns the mangled name of function `f`.
  func llvmName(of f: IRFunction.Name) -> String {
    // FIXME: use actual mangling.
    if case .lowered(let d) = f,
      let decl = cast(d, to: FunctionDeclaration.self)
    {
      // @extern("name"): skip mangling and use the provided raw symbol name.
      // @extern (no arg): skip mangling and use the function's bare identifier.
      if isExtern(decl) {
        if let raw = self[decl].annotations
          .first(where: { $0.identifier.value == "extern" })
          .flatMap({ $0.arguments.uniqueElement })
          .flatMap({ $0.value.string })
        {
          return raw
        }
        return self[decl].identifier.value.description
      }

      if let s = symbol(annotating: decl) {
        return s
      }
    }

    var p = TreePrinter(program: self) // todo
    return "hylo_" + f.show(using: &p)
  }
}

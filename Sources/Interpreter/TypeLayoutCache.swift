import FrontEnd
import Utilities

/// A memoizing computer of type layouts.
struct TypeLayoutCache {

  /// The program supplying the types.
  let p: Program

  /// The ABI for which the types will be laid out.
  let abi: any TargetABI

  /// The memo of layouts computed so far.
  private var storage: [MonomorphicTypeIdentity: TypeLayout] = [:]

  /// An instance for laying out types in `p` according to `abi`.
  public init(typesIn p: Program, for abi: any TargetABI) {
    self.p = p
    self.abi = abi
  }

  /// The layout for `t`.
  public subscript(_ t: MonomorphicTypeIdentity) -> TypeLayout {
    mutating get {
      if let r = storage[t] { return r }
      let r = computeLayout(t)
      storage[t] = r
      return r
    }
  }

  /// Returns the layout for `t`.
  private mutating func computeLayout(_ t: MonomorphicTypeIdentity) -> TypeLayout {
    if isMachineType(t.underlying) {
      let u = type(t.underlying, as: MachineType.self)
      return TypeLayout(bytes: abi.layout(u), type: t, parts: [], isEnumLayout: false)
    } else if isEnum(t.underlying) {
      unimplemented()
    } else if isStruct(t.underlying) {
      return computeLayout(struct: t)
    } else if isTuple(t.underlying) {
      return computeLayout(tuple: t)
    } else {
      unreachable("\(p.show(t.underlying)) doesn't have any layout)")
    }
  }

  /// Returns the layout for struct `t`.
  private mutating func computeLayout(struct t: MonomorphicTypeIdentity) -> TypeLayout {
    unimplemented()
  }

  /// Returns the layout for tuple `t`.
  private mutating func computeLayout(tuple t: MonomorphicTypeIdentity) -> TypeLayout {
    // let u = type(t.underlying, as: Tuple.self)
    unimplemented()
  }

  /// Returns true iff `t` is of `MachineType`.
  private func isMachineType(_ t: AnyTypeIdentity) -> Bool {
    tag(t) == MachineType.self
  }

  /// Returns true iff `t` is of enum type.
  private func isEnum(_ t: AnyTypeIdentity) -> Bool {
    let u = tag(t)
    if u == Enum.self {
      return true
    } else if u == TypeApplication.self {
      return isEnum(type(t, as: TypeApplication.self).abstraction)
    } else {
      return false
    }
  }

  /// Returns true iff `t` is a `Struct`.
  private func isStruct(_ t: AnyTypeIdentity) -> Bool {
    let u = tag(t)
    if u == Struct.self {
      return true
    } else if u == TypeApplication.self {
      return isStruct(type(t, as: TypeApplication.self).abstraction)
    } else {
      return false
    }
  }

  /// Returns true iff `t` is a `Tuple`.
  private func isTuple(_ t: AnyTypeIdentity) -> Bool {
    let u = tag(t)
    if u == Tuple.self {
      return true
    } else if u == TypeApplication.self {
      return isTuple(type(t, as: TypeApplication.self).abstraction)
    } else {
      return false
    }
  }

  /// Returns the type identified by `t`, cast to `U`.
  private func type<U: TypeTree>(_ t: AnyTypeIdentity, as u: U.Type) -> U {
    p.types[p.types.cast(t, to: u)!]
  }

  /// Returns the tag of `t`.
  private func tag(_ t: AnyTypeIdentity) -> any TypeTree.Type {
    p.types.tag(of: t).value
  }
}

import FrontEnd
import Utilities

/// A memoizing computer of type layouts.
struct TypeLayoutCache {

  /// The program supplying the types.
  var p: Program

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
    let d = p.declaration(of: t.underlying)!
    let m = p.parent(containing: d).module
    let ms = p.storage(of: t.underlying, visibleFrom: m)!
    return computeLayout(
      record: t,
      havingMembers: ms.map {
        (type: MonomorphicTypeIdentity($0), label: nil)
      })
  }

  /// Returns the layout for tuple `t`.
  private mutating func computeLayout(tuple t: MonomorphicTypeIdentity) -> TypeLayout {
    let u = ConcreteTypeIdentity<Tuple>(uncheckedFrom: t.underlying)
    let (ms, o) = p.types.members(of: u)
    assert(o == false)
    return computeLayout(
      record: t,
      havingMembers: ms.map {
        (type: MonomorphicTypeIdentity($0), label: nil)
      }
    )
  }

  /// Returns the layout for a record `t` having members `ms`.
  private mutating func computeLayout(
    record t: MonomorphicTypeIdentity,
    havingMembers ms: [(type: MonomorphicTypeIdentity, label: String?)]
  ) -> TypeLayout {
    if ms.isEmpty {
      return TypeLayout(
        bytes: .init(alignment: 1, size: 0), type: t,
        parts: [], isEnumLayout: false
      )
    }
    let f = ms.first!
    var b = self[f.type].bytes
    var parts: [TypeLayout.Part] = [.init(name: f.label ?? "0", type: f.type, offset: 0)]
    for (i, p) in ms.enumerated().dropFirst() {
      let c = self[p.type].bytes
      b = b.appending(c)
      parts.append(
        .init(
          name: p.label ?? String(describing: i + 1),
          type: p.type, offset: b.size - c.size))
    }
    return TypeLayout(bytes: b, type: t, parts: parts, isEnumLayout: false)
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

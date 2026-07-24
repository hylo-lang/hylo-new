import FrontEnd
import Utilities

/// A memoizing computer of type layouts.
struct TypeLayoutCache {

  /// The ABI for which the types will be laid out.
  let abi: any TargetABI

  /// The memo of layouts computed so far.
  private var storage: [MonomorphicTypeIdentity: TypeLayout] = [:]

  /// An instance for laying out types according to `abi`.
  public init(for abi: any TargetABI) {
    self.abi = abi
  }

  /// The layout for `t` in `p`.
  public mutating func layout(
    _ t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if let r = storage[t] { return r }
    let r = computeLayout(t, in: &p)
    storage[t] = r
    return r
  }

  /// Returns the layout for `t` in `p`.
  ///
  /// - Precondition: `t` is not an alias.
  private mutating func computeLayout(
    _ t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if t.underlying[.hasAliases] {
      let l = layout(.init(p.types.dealiased(t.underlying)), in: &p)
      return .init(bytes: l.bytes, type: t, parts: l.parts, isEnumLayout: l.isEnumLayout)
    }
    let u = tag(t.underlying, in: p)
    if u == MachineType.self {
      let u = type(t.underlying, as: MachineType.self, in: p)
      return TypeLayout(bytes: abi.layout(u), type: t, parts: [], isEnumLayout: false)
    } else if hasRecordLayout(t.underlying, in: p) {
      return computeLayout(record: t, in: &p)
    } else if hasEnumLayout(t.underlying, in: p) {
      return computeLayout(enum: t, in: &p)
    } else {
      unreachable("\(p.show(t.underlying)) doesn't have any layout)")
    }
  }

  /// Returns the layout for record `t` in `p`.
  private mutating func computeLayout(
    record t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let ms = storage(record: t.underlying, in: &p)
    return computeLayout(
      record: t,
      havingMembers: ms.map {
        (type: MonomorphicTypeIdentity($0), label: nil)
      },
      in: &p
    )
  }

  /// Returns the layout for a record `t` in `p` having members `ms`.
  private mutating func computeLayout(
    record t: MonomorphicTypeIdentity,
    havingMembers ms: [(type: MonomorphicTypeIdentity, label: String?)],
    in p: inout Program
  ) -> TypeLayout {
    var b = TypeLayout.Bytes(alignment: 1, size: 0)
    var parts: [TypeLayout.Part] = []
    for (i, m) in ms.enumerated() {
      let c = layout(m.type, in: &p).bytes
      b = b.appending(c)
      parts.append(
        .init(name: m.label ?? String(i), type: m.type, offset: b.size - c.size))
    }
    return TypeLayout(bytes: b, type: t, parts: parts, isEnumLayout: false)
  }

  /// Returns the layout for an enum `t` in `p`.
  private mutating func computeLayout(
    enum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if isTaggedEnum(t.underlying, in: p) {
      computeLayout(taggedEnum: t, in: &p)
    } else {
      computeLayout(rawEnum: t, in: &p)
    }
  }

  /// Returns the layout for a tagged enum `t` in `p`.
  private mutating func computeLayout(
    taggedEnum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let basis = storage(nominal: t.underlying, in: &p)
      .map { layout(MonomorphicTypeIdentity($0), in: &p) }

    if basis.count == 0 {
      return TypeLayout(
        bytes: .init(alignment: 1, size: 0), type: t,
        parts: [], isEnumLayout: true)
    }

    let discriminator = abi.enumDiscriminator(count: basis.count, in: &p)
    let discriminatorLayout = layout(discriminator, in: &p)

    let payloadBytes = TypeLayout.Bytes(
      alignment: basis.lazy.map(\.alignment).max()!,
      size: basis.lazy.map(\.size).max()!)

    let payloadFirst = payloadBytes.appending(discriminatorLayout.bytes)
    let discriminatorFirst = discriminatorLayout.bytes.appending(payloadBytes)

    let payloadOffset: Int
    let discriminatorOffset: Int
    let l: TypeLayout.Bytes

    if payloadFirst.size < discriminatorFirst.size {
      l = payloadFirst
      payloadOffset = 0
      discriminatorOffset = l.size - discriminatorLayout.size
    } else {
      l = discriminatorFirst
      payloadOffset = l.size - payloadBytes.size
      discriminatorOffset = 0
    }

    return TypeLayout(
      bytes: l,
      type: t,
      parts:
        basis.map { .init(name: String(describing: $0.type), type: $0.type, offset: payloadOffset) }
        + [.init(name: "discriminator", type: discriminator, offset: discriminatorOffset)],
      isEnumLayout: true)
  }

  /// Returns the layout for a raw enum `t` in `p`.
  private mutating func computeLayout(
    rawEnum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    let discriminator = MonomorphicTypeIdentity(
      storage(nominal: t.underlying, in: &p).first!)
    let discriminatorLayout = layout(discriminator, in: &p)
    return TypeLayout(
      bytes: discriminatorLayout.bytes,
      type: t,
      parts: [.init(name: "discriminator", type: discriminator, offset: 0)],
      isEnumLayout: true
    )
  }

  /// Returns true iff `t` in `p` has a record layout.
  private func hasRecordLayout(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    precondition(!t[.hasAliases])
    let u = tag(t, in: p)
    if u == Struct.self || u == Tuple.self {
      return true
    } else if u == TypeApplication.self {
      let a = type(t, as: TypeApplication.self, in: p)
      let v = tag(a.abstraction, in: p)
      return v == Struct.self || v == Tuple.self
    } else {
      return false
    }
  }

  /// Returns true iff `t` in `p` has an enum layout.
  private func hasEnumLayout(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    precondition(!t[.hasAliases])
    let u = tag(t, in: p)
    if u == Enum.self {
      return true
    } else if u == TypeApplication.self {
      let a = type(t, as: TypeApplication.self, in: p)
      let v = tag(a.abstraction, in: p)
      return v == Enum.self
    } else {
      return false
    }
  }

  /// Returns true iff enum `t` in `p` has a representation.
  private func isTaggedEnum(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    precondition(!t[.hasAliases])
    let u = tag(t, in: p)
    if u == Enum.self {
      let d = type(t, as: Enum.self, in: p).declaration
      return p[d].representation == nil
    } else {
      let a = type(t, as: TypeApplication.self, in: p)
      let d = type(a.abstraction, as: Enum.self, in: p).declaration
      return p[d].representation == nil
    }
  }

  /// Returns the types of stored parts of record `t` in `p`.
  private func storage(record t: AnyTypeIdentity, in p: inout Program) -> [AnyTypeIdentity] {
    let u = tag(t, in: p)
    if u == Tuple.self {
      let v = ConcreteTypeIdentity<Tuple>(uncheckedFrom: t)
      let (ms, o) = p.types.members(of: v)
      assert(o == false)
      return ms
    } else {
      return storage(nominal: t, in: &p)
    }
  }

  /// Returns the types of stored parts of nominal `t` in `p`.
  private func storage(nominal t: AnyTypeIdentity, in p: inout Program) -> [AnyTypeIdentity] {
    let d = p.declaration(of: t)!
    let m = p.parent(containing: d).module
    return p.storage(of: t, visibleFrom: m)!
  }

  /// Returns the type identified by `t` in `p`, cast to `U`.
  private func type<U: TypeTree>(
    _ t: AnyTypeIdentity, as u: U.Type,
    in p: Program
  ) -> U {
    p.types[p.types.cast(t, to: u)!]
  }

  /// Returns the tag of `t` in `p`.
  private func tag(_ t: AnyTypeIdentity, in p: Program) -> any TypeTree.Type {
    p.types.tag(of: t).value
  }
}

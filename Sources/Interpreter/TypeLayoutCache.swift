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
    let ns =
      names(record: t.underlying, in: &p)
      ?? .init(repeating: nil, count: ms.count)
    return computeLayout(
      record: t,
      havingMembers: zip(ms, ns).map { .init(name: $0.1, type: .init($0.0)) },
      in: &p)
  }

  /// Returns the layout for a record `t` in `p` whose members are `ms` in
  /// declaration order.
  private mutating func computeLayout(
    record t: MonomorphicTypeIdentity,
    havingMembers ms: [TypeLayout.Member],
    in p: inout Program
  ) -> TypeLayout {
    let l = storageLayoutOfRecord(
      havingMembers: ms.map { layout($0.type, in: &p).bytes })

    let parts = zip(ms, l.partOffsets).enumerated().map { i, x in
      let (m, o) = x
      return TypeLayout.Part(
        name: m.name ?? String(i),
        type: m.type,
        offset: o
      )
    }

    return .init(bytes: l.bytes, type: t, parts: parts, isEnumLayout: false)
  }

  /// Returns the layout for an enum `t` in `p`.
  private mutating func computeLayout(
    enum t: MonomorphicTypeIdentity,
    in p: inout Program
  ) -> TypeLayout {
    if isRawValueEnum(t.underlying, in: p) {
      return computeLayout(rawValueEnum: t, in: &p)
    }
    let cases = storage(nominal: t.underlying, in: &p).map { c in
      layout(.init(c), in: &p)
    }

    let d = layout(abi.enumDiscriminator(count: cases.count, in: &p), in: &p)

    let payload = TypeLayout.Bytes(
      alignment: cases.map(\.alignment).max() ?? 1,
      size: cases.map(\.size).max() ?? 0)

    let l = storageLayoutOfRecord(havingMembers: [
        payload, .init(alignment: d.alignment, size: d.size),
    ])

    let ns = names(enum: t.underlying, in: &p)
    let parts =
      zip(cases, ns).map { TypeLayout.Part(name: $0.1, type: $0.0.type, offset: l.partOffsets[0]) }
      + [.init(name: "discriminator", type: d.type, offset: l.partOffsets[1])]


    return .init(bytes: l.bytes, type: t, parts: parts, isEnumLayout: true)
  }

  /// Returns the layout for a raw value enum `t` in `p`.
  private mutating func computeLayout(
    rawValueEnum t: MonomorphicTypeIdentity,
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

  /// Returns true iff enum `t` in `p` is a raw value enum.
  private func isRawValueEnum(_ t: AnyTypeIdentity, in p: Program) -> Bool {
    precondition(!t[.hasAliases])
    let u = tag(t, in: p)
    if u == Enum.self {
      let d = type(t, as: Enum.self, in: p).declaration
      return p[d].representation != nil
    } else {
      let a = type(t, as: TypeApplication.self, in: p)
      let d = type(a.abstraction, as: Enum.self, in: p).declaration
      return p[d].representation != nil
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

  /// Returns the declared names (if any) of stored parts of record `t` in `p`,
  /// in storage order.
  private func names(record t: AnyTypeIdentity, in p: inout Program) -> [String?]? {
    precondition(!t[.hasAliases])
    guard let d = p.declaration(of: t) else { return nil }
    let s = p.cast(d, to: StructDeclaration.self)!
    return p.storedProperties(of: s).map { p[$0].identifier.value }
  }

  /// Returns the declared names of stored parts of enum `t` in `p`,
  /// in storage order.
  private func names(enum t: AnyTypeIdentity, in p: inout Program) -> [String] {
    precondition(!t[.hasAliases])
    let d = p.declaration(of: t)!
    let e = p.cast(d, to: EnumDeclaration.self)!
    return p[e].members
      .compactMap { p.cast($0, to: EnumCaseDeclaration.self) }
      .map { p[$0].identifier.value }
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

/// Returns the storage layout and part offsets of a record having members
/// with layouts `ms` in declaration order.
func storageLayoutOfRecord(
  havingMembers ms: [TypeLayout.Bytes]
) -> (bytes: TypeLayout.Bytes, partOffsets: [Int]) {
  let storageOrder = ms.enumerated().sorted {
    if $0.element.alignment == $1.element.alignment {
      return $0.offset < $1.offset
    } else {
      return $0.element.alignment > $1.element.alignment
    }
  }

  var b = TypeLayout.Bytes(alignment: 1, size: 0)
  var offsets = [Int](repeating: 0, count: ms.count)
  for (i, m) in storageOrder {
    b = b.appending(m)
    offsets[i] = b.size - m.size
  }
  return (b, offsets)
}

import FrontEnd
import Utilities

/// The memory layout of a type, described without reference to the compiler's representation of
/// types.
///
/// Instances are meant to be reported to clients that have no access to the compiler's internal
/// data structures, such as a tool answering layout queries from a WebAssembly guest.
public struct LayoutDescription: Regular, Codable {

  /// A region of a source file, as 1-based lines and 1-based UTF-16 offsets.
  ///
  /// Offsets are counted in UTF-16 code units because that is the unit an editor showing the
  /// source will address it in.
  public struct SourceRegion: Regular, Codable {

    /// The line on which the region starts.
    public let line: Int

    /// The offset at which the region starts.
    public let column: Int

    /// The line on which the region ends.
    public let endLine: Int

    /// The offset at which the region ends.
    public let endColumn: Int

    /// Creates an instance with the given properties.
    public init(line: Int, column: Int, endLine: Int, endColumn: Int) {
      self.line = line
      self.column = column
      self.endLine = endLine
      self.endColumn = endColumn
    }

    /// Creates an instance denoting `s`.
    public init(_ s: SourceSpan) {
      let a = SourcePosition(s.region.lowerBound, in: s.source).lineAndUTF16Offset
      let b = SourcePosition(s.region.upperBound, in: s.source).lineAndUTF16Offset
      self.init(
        line: a.line + 1, column: a.offset + 1, endLine: b.line + 1, endColumn: b.offset + 1)
    }

  }

  /// A part of a laid out type, and where it is stored in an instance.
  public struct Part: Regular, Codable {

    /// The name of the part.
    public let name: String

    /// A textual representation of the type of the part.
    public let type: String

    /// The byte offset of the part relative to the start of an instance.
    public let offset: Int

    /// The number of bytes occupied by an instance of the part's type.
    public let size: Int

    /// The minimum alignment of an instance of the part's type.
    public let alignment: Int

    /// Where the part was declared, or `nil` if it was not declared in the queried module.
    public let site: SourceRegion?

    /// The parts of this part's own type, empty if it has none.
    ///
    /// Their offsets are relative to the same instance this part belongs to, not to this part, so
    /// that a client drawing an instance's bytes can read every offset the same way.
    public let parts: [Part]

    /// `true` iff this part's type is an enum, whose own parts overlap.
    public let isEnum: Bool

    /// Creates an instance with the given properties.
    public init(
      name: String, type: String, offset: Int, size: Int, alignment: Int,
      site: SourceRegion? = nil, parts: [Part] = [], isEnum: Bool = false
    ) {
      self.name = name
      self.type = type
      self.offset = offset
      self.size = size
      self.alignment = alignment
      self.site = site
      self.parts = parts
      self.isEnum = isEnum
    }

  }

  /// A textual representation of the type whose layout is described by `self`.
  public let type: String

  /// The number of bytes occupied by an instance.
  public let size: Int

  /// The minimum alignment of an instance.
  public let alignment: Int

  /// `true` iff the described type is an enum.
  ///
  /// All the parts of an enum layout but the last denote mutually exclusive payloads, stored at
  /// the same offset. The last denotes the discriminator.
  public let isEnum: Bool

  /// The parts of the described type, in declaration order.
  public let parts: [Part]

  /// Where the type was declared, or `nil` if it was not declared in the queried module.
  public let site: SourceRegion?

  /// Creates an instance with the given properties.
  public init(
    type: String, size: Int, alignment: Int, isEnum: Bool, parts: [Part],
    site: SourceRegion? = nil
  ) {
    self.type = type
    self.size = size
    self.alignment = alignment
    self.isEnum = isEnum
    self.parts = parts
    self.site = site
  }

}

/// A memoizing computer of type layout descriptions.
///
/// Unlike the layouts computed by `TypeLayoutCache`, which refer to the compiler's representation
/// of types, the descriptions computed by an instance of this type are self-contained. They can be
/// reported to a client having no access to that representation.
public struct LayoutQuery {

  /// The layouts computed so far.
  private var cache: TypeLayoutCache

  /// An instance laying types out for `UnrealABI`, which is the only ABI the compiler describes so
  /// far.
  public init() {
    self.cache = .init(for: UnrealABI())
  }

  /// Returns the layout of each distinct type declared in `m`, which is defined in `p`.
  ///
  /// - Precondition: `m` has been type checked and does not contain any error.
  public mutating func layoutsOfTypesDeclared(
    in m: Module.ID, of p: inout Program
  ) -> [LayoutDescription] {
    var seen: Set<AnyTypeIdentity> = []
    var result: [LayoutDescription] = []
    for n in p.select(from: m, .all) {
      guard
        let d = p.castToDeclaration(n), let t = denotedType(of: d, in: p),
        seen.insert(t).inserted, hasLayout(t, in: &p)
      else { continue }

      let l = cache.layout(.init(t), in: &p)
      result.append(description(of: l, declaredIn: m, of: &p))
    }
    return result
  }

  /// Returns the layout of the type denoted by the innermost tree of `f` containing `i`, where `f`
  /// is a source file of `p`, or `nil` if no such tree denotes a type having a layout.
  ///
  /// This is the layout counterpart of an editor's hover: `i` is the position of a cursor and the
  /// answer describes whatever it is on, be it a type expression or an expression having a type.
  ///
  /// - Precondition: the module containing `f` has been type checked and does not contain any
  ///   error.
  public mutating func layout(
    ofTypeAt i: SourceFile.Index, in f: SourceFile.ID, of p: inout Program
  ) -> LayoutDescription? {
    var finder = InnermostTreeFinder(containing: i)
    p.visit(p.topLevelDeclarations(in: f), calling: &finder)

    guard let n = finder.result, let u = p.type(maybeAssignedTo: n) else { return nil }

    // A type expression is assigned a metatype; any other tree is assigned the type of its value.
    let t = p.types.cast(u, to: Metatype.self).map({ (m) in p.types[m].inhabitant }) ?? u
    guard hasLayout(t, in: &p) else { return nil }

    let l = cache.layout(.init(t), in: &p)
    return description(of: l, declaredIn: f.module, of: &p)
  }

  /// Returns the type denoted by `d`, which is defined in `p`, or `nil` if `d` denotes no type.
  private func denotedType(of d: DeclarationIdentity, in p: Program) -> AnyTypeIdentity? {
    guard
      let u = p.type(maybeAssignedTo: d), let m = p.types.cast(u, to: Metatype.self)
    else { return nil }
    return p.types[m].inhabitant
  }

  /// Returns `true` iff the layout of `t`, which is defined in `p`, can be computed.
  ///
  /// This check does not look at the parts of `t`, whose types are not part of its tree. Laying
  /// out a record declared in a module containing errors may therefore still be impossible.
  private func hasLayout(_ t: AnyTypeIdentity, in p: inout Program) -> Bool {
    if t[.hasError] || t[.hasGenericParameter] || t[.hasVariable] { return false }
    let s = p.tag(p.underlyingType(t))
    return (s == MachineType.self) || (s == Struct.self) || (s == Tuple.self) || (s == Enum.self)
  }

  /// Returns a description of `l`, whose type is defined in `p`, reporting the source regions of
  /// whatever `m` declares.
  ///
  /// Only `m`'s regions are reported because they are the ones a client showing that module's
  /// source can point at. A type the query reached through the standard library has a region too,
  /// in a file the client does not have.
  private mutating func description(
    of l: TypeLayout, declaredIn m: Module.ID, of p: inout Program
  ) -> LayoutDescription {
    .init(
      type: p.show(l.type.underlying), size: l.size, alignment: l.alignment,
      isEnum: l.isEnumLayout, parts: parts(of: l, at: 0, declaredIn: m, of: &p),
      site: declarationSite(of: l.type.underlying, declaredIn: m, of: &p))
  }

  /// Returns the parts of `l`, and of their types in turn, as offsets from `base`.
  ///
  /// The nesting is reported rather than flattened because it is what a client draws: a member
  /// whose type is a record is one member holding two, not two members side by side, and nothing
  /// downstream can tell the difference from a list of offsets. Working it out here costs nothing,
  /// since laying a part out already lays out its type.
  private mutating func parts(
    of l: TypeLayout, at base: Int, declaredIn m: Module.ID, of p: inout Program
  ) -> [LayoutDescription.Part] {
    let sites = partSites(of: l, declaredIn: m, of: &p)
    var result: [LayoutDescription.Part] = []
    for (i, q) in l.parts.enumerated() {
      let r = cache.layout(q.type, in: &p)
      let at = base + q.offset
      result.append(
        .init(
          name: q.name ?? "", type: p.show(q.type.underlying), offset: at,
          size: r.size, alignment: r.alignment, site: i < sites.count ? sites[i] : nil,
          parts: parts(of: r, at: at, declaredIn: m, of: &p), isEnum: r.isEnumLayout))
    }
    return result
  }

  /// Returns where each part of `l` was declared, using `nil` for the parts that `m` does not
  /// declare, and stopping early where the declarations run out.
  private func partSites(
    of l: TypeLayout, declaredIn m: Module.ID, of p: inout Program
  ) -> [LayoutDescription.SourceRegion?] {
    guard let d = declaration(of: l.type.underlying, declaredIn: m, of: &p) else { return [] }

    if let s = p.cast(d, to: StructDeclaration.self) {
      return p.storedProperties(of: s).map { (v) in .init(p[v].site) }
    } else if let e = p.cast(d, to: EnumDeclaration.self) {
      // The discriminator is a part with no declaration, and it comes last.
      return p[e].members.compactMap({ (n) in p.cast(n, to: EnumCaseDeclaration.self) })
        .map { (c) in .init(p[c].site) }
    } else {
      return []
    }
  }

  /// Returns where `t` was declared, or `nil` if `m` does not declare it.
  private func declarationSite(
    of t: AnyTypeIdentity, declaredIn m: Module.ID, of p: inout Program
  ) -> LayoutDescription.SourceRegion? {
    declaration(of: t, declaredIn: m, of: &p).map { (d) in .init(p[d].site) }
  }

  /// Returns the declaration of `t` if `m` declares it, and `nil` otherwise.
  private func declaration(
    of t: AnyTypeIdentity, declaredIn m: Module.ID, of p: inout Program
  ) -> DeclarationIdentity? {
    let u = p.underlyingType(t)
    guard let d = p.declaration(of: u), d.module == m else { return nil }
    return d
  }


}

/// A syntax visitor that finds the innermost tree containing a given index.
///
/// The traversal mirrors the one with which the Hylo language server answers hover requests.
private struct InnermostTreeFinder: SyntaxVisitor {

  /// The index that the sought tree must contain.
  private let target: SourceFile.Index

  /// The innermost tree seen so far whose site contains `target`, if any.
  private(set) var result: AnySyntaxIdentity? = nil

  /// The site of `result`.
  private var narrowest: Range<SourceFile.Index>? = nil

  /// Creates an instance looking for the innermost tree containing `i`.
  init(containing i: SourceFile.Index) {
    self.target = i
  }

  mutating func willEnter(_ n: AnySyntaxIdentity, in program: Program) -> Bool {
    // The upper bound is included so that a cursor sitting at the end of a name selects it.
    let s = program[n].site.region
    if (s.lowerBound > target) || (target > s.upperBound) {
      // The children of a scope are strictly contained in it.
      return !program.isScope(n)
    }

    // Trees are visited in pre-order, so a site contained in the narrowest one seen so far belongs
    // to a deeper tree.
    if let w = narrowest, (s.lowerBound < w.lowerBound) || (s.upperBound > w.upperBound) {
      return true
    }
    narrowest = s
    result = n
    return true
  }

}

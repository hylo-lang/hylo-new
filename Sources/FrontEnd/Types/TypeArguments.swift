import Archivist
import OrderedCollections

/// The arguments of a type application.
public struct TypeArguments: Sendable {

  /// The internal representation of `TypeArguments`.
  public typealias Contents = OrderedDictionary<GenericParameter.ID, AnyTypeIdentity>

  /// A table mapping formal type parameters to arguments.
  private var contents: Contents

  /// Creates an empty instance.
  public init() {
    self.contents = [:]
  }

  /// Creates an instance wrapping the given dictionary.
  public init(_ contents: Contents) {
    self.contents = contents
  }

  /// Creates an new dictionary from the key-value pairs in `parametersWithValues`.
  public init<S: Sequence<(GenericParameter.ID, AnyTypeIdentity)>>(parametersWithValues: S) {
    self.contents = .init(uniqueKeysWithValues: parametersWithValues)
  }

  /// Creates an instance mapping each parameter in `ps` to its corresponding argument in `ts`.
  public init<P: Collection<GenericParameter.ID>, A: Collection<AnyTypeIdentity>>(
    mapping ps: P, to ts: A
  ) {
    assert(ps.count == ts.count)
    self.contents = .init(minimumCapacity: ps.count)
    for (p, t) in zip(ps, ts) {
      self.contents[p] = t
    }
  }

  /// Creates an instance mapping each parameter in `ps` to `makeArgument` applied on it.
  public init<P: Collection<GenericParameter.ID>>(
    mapping ps: P, to makeArgument: (GenericParameter.ID) -> AnyTypeIdentity
  ) {
    self.contents = .init(minimumCapacity: ps.count)
    for p in ps {
      self.contents[p] = makeArgument(p)
    }
  }

  /// `true` iff `self` is empty.
  public var isEmpty: Bool {
    contents.isEmpty
  }

  /// The number of elements in `self`.
  public var count: Int {
    contents.count
  }

  /// A sequence presenting the contents of `self`, in order.
  public var elements: Contents.Elements {
    contents.elements
  }

  /// The formal parameters in `self`, in order.
  public var parameters: OrderedSet<GenericParameter.ID> {
    contents.keys
  }

  /// The arguments in `self`, in order.
  public var values: Contents.Values {
    contents.values
  }

  /// Accesses the element at `p`.
  public subscript(p: GenericParameter.ID) -> AnyTypeIdentity? {
    get { self.contents[p] }
    set { self.contents[p] = newValue }
  }

  /// Returns a new instance mapping the parameters in `self` to their corresponding type argument
  /// transformed by `transform`.
  public func mapValues(_ transform: (AnyTypeIdentity) -> AnyTypeIdentity) -> TypeArguments {
    .init(contents.mapValues(transform))
  }

}

extension TypeArguments: ExpressibleByDictionaryLiteral {

  public init(dictionaryLiteral elements: (GenericParameter.ID, AnyTypeIdentity)...) {
    self.contents = .init(uniqueKeysWithValues: elements)
  }

}

extension TypeArguments: Equatable {}

extension TypeArguments: Hashable {}

extension TypeArguments: Showable {

  public func show(using printer: inout TreePrinter) -> String {
    var first = true
    let s = contents.reduce(into: "[") { (s, e) in
      if first { first = false } else { s.append(", ") }
      s.append("\(printer.show(e.key)): \(printer.show(e.value))")
    }
    return s + "]"
  }

}

extension TypeArguments: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let count = try Int(archive.readUnsignedLEB128())
    self.contents = .init(minimumCapacity: count)
    for _ in 0 ..< count {
      let k = try archive.read(GenericParameter.ID.self, in: &context)
      let v = try archive.read(AnyTypeIdentity.self, in: &context)
      self.contents[k] = v
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try contents.elements.write(to: &archive) { (e, a) in
      try e.key.write(to: &a, in: &context)
      try e.value.write(to: &a, in: &context)
    }
  }

}

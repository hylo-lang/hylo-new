import Algorithms
import Utilities

/// The evaluation context of an abstract interpreter.
internal struct AbstractContext<Domain: AbstractDomain>: Hashable, Sendable {

  /// A mapping from register and parameter to their value in an abstract context.
  ///
  /// The order in which the contents of the mapping are laid out is consistent across all
  /// instances and the conformance of `Locals` to `Collection` yields deterministic iterations.
  internal struct Locals: Hashable, Sendable {

    /// A parameter or register in the IR.
    private struct Key: Hashable, Comparable, Sendable {

      /// The value of this key.
      let value: IRValue

      static func < (l: Key, r: Key) -> Bool {
        switch (l.value, r.value) {
        case (.parameter(let i), .parameter(let j)):
          return i < j
        case (.parameter, .register):
          return true
        case (.register, .parameter):
          return false
        case (.register(let i), .register(let j)):
          return i < j
        default:
          fatalError("incomparable keys")
        }
      }

    }

    /// The contents of this mapping.
    private var contents: SortedDictionary<Key, AbstractValue<Domain>>

    /// Creates an empty context.
    fileprivate init() {
      self.contents = [:]
    }

    /// Accesses the value at assigned to `key`, which is either a register or a parameter.
    ///
    /// - Complexity: O(log n) where n is the number en key/value pairs in `self`.
    internal subscript(key: IRValue) -> AbstractValue<Domain>? {
      get {
        contents[.init(value: key)]
      }
      _modify {
        yield &contents[.init(value: key)]
      }
    }

    /// Merges `other` into `self`.
    fileprivate mutating func merge(_ other: Self) {
      var l = 0
      var r = 0

      while l < self.contents.count {
        if r >= other.contents.count {
          self.contents.removeLast(self.contents.count - l)
          break
        } else if self.contents[l].key < other.contents[r].key {
          self.contents.remove(at: l)
        } else if self.contents[l].key > other.contents[r].key {
          r += 1
        } else {
          self.contents.updateValue(self.contents[l].value && other.contents[r].value, at: l)
          l += 1
          r += 1
        }
      }
    }

    /// Removes all key/value pairs satisfying `predicate`.
    internal mutating func removeAll(where predicate: (IRValue, AbstractValue<Domain>) -> Bool) {
      contents.removeAll(where: { (k, v) in predicate(k.value, v) })
    }

  }

  /// The values assigned to registers and parameters.
  internal var locals: Locals = .init()

  /// The state of memory.
  internal var memory: [IRValue: AbstractObject<Domain>] = [:]

  /// `true` iff the context contains an error.
  internal private(set) var containsError: Bool = false

  /// Creates an empty context.
  internal init() {}

  /// Merges `other` into `self`.
  internal mutating func merge(_ other: Self) {
    self.locals.merge(other.locals)
    self.memory.merge(other.memory, uniquingKeysWith: &&)
    self.containsError = self.containsError || other.containsError
  }

  /// Sets the flag indicating that an error was encountered in this context.
  internal mutating func setError() {}

  /// Returns the result calling `action` with a projection of the object at `place`, using `typer`
  /// to compute abstract layouts.
  internal mutating func withObject<T>(
    at place: AbstractPlace, computingLayoutWith typer: inout Typer,
    _ action: (inout AbstractObject<Domain>, inout Typer) -> T
  ) -> T {
    switch place {
    case .root(let root):
      return action(&memory[root]!, &typer)
    case .subplace(let root, let path):
      if path.isEmpty {
        return action(&memory[root]!, &typer)
      } else {
        return modify(&memory[root]!) { (o) in
          o.withSubobject(at: path, computingLayoutWith: &typer, action)
        }
      }
    }
  }

  /// Sets the value of the object at `place` using `typer` to compute abstract layouts.
  internal mutating func updateValue(
    _ value: AbstractObject<Domain>.Value, at place: AbstractPlace,
    computingLayoutWith typer: inout Typer
  ) {
    withObject(at: place, computingLayoutWith: &typer, { (o, _) in o.value = value })
  }

  /// Updates `self` to define register `i`, which is in `f`.
  ///
  /// `i` identifies a register in `f` that results in either an object or a place. In the first
  /// case, an new object is assigned to `i` directly. In the second case, a new place is created
  /// to contain the new object and the register is assigned to that place.
  ///
  /// The new object is defined as a uniform value `v`.
  internal mutating func declare<T: InstructionIdentity>(
    _ i: T, from f: IRFunction, initially v: Domain
  ) {
    // Create a new object.
    let t = f.resolved(f.at(i.erased).type)!
    let o = AbstractObject(type: t.type, value: .uniform(v))

    // If the register defines an address, create a new place and assigns it the new object.
    if t.isPlace {
      memory[.register(i.erased)] = .init(type: t.type, value: .uniform(v))
      locals[.register(i.erased)] = .place(.root(.register(i.erased)))
    }

    // Otherwise, assigns the new object to the register itself.
    else {
      locals[.register(i.erased)] = .object(o)
    }
  }

}

extension AbstractContext.Locals: RandomAccessCollection {

  internal typealias Element = (key: IRValue, value: AbstractValue<Domain>)

  internal typealias Index = Int

  internal var startIndex: Int { 0 }

  internal var endIndex: Int { contents.count }

  internal func index(after p: Int) -> Int { p + 1 }

  internal func index(before p: Index) -> Index { p - 1 }

  internal subscript(p: Int) -> (key: IRValue, value: AbstractValue<Domain>) {
    (contents[p].key.value, contents[p].value)
  }

}

extension AbstractContext: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    let ls = printer.show(locals)
    let ms = memory
      .sorted(by: \.key, using: Self.areInIncreasingOrder(_:_:))
      .reduce(into: "", { (s, p) in s += "\(printer.show(p.key)) ↦ \(printer.show(p.value))\n" })

    return """
      locals:
      \(ls.indented)
      memory:
      \(ms.indented)
      """
  }

  /// Returns `true` iff `l` precedes `r` when computing whether two abstract places are in order.
  private static func areInIncreasingOrder(_ l: IRValue, _ r: IRValue) -> Bool {
    switch (l, r) {
    case (.parameter(let a), .parameter(let b)):
      return a < b
    case (.parameter, _):
      return true
    case (.register, .parameter):
      return false
    case (.register(let a), .register(let b)):
      return a < b
    default:
      fatalError()
    }
  }

}

extension AbstractContext.Locals: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    self.reduce(into: "") { (result, pair) in
      result += "\(printer.show(pair.key)) ↦ \(printer.show(pair.value))\n"
    }
  }

}

import Algorithms
import Utilities

/// The evaluation context of an abstract interpreter.
internal struct AbstractContext<Domain: AbstractDomain>: Hashable, Sendable {

  /// A mapping from register and parameter to their value in an abstract context.
  ///
  /// The order in which the contents of the mapping are laid out is consistent across all
  /// instances and the conformance of `Locals` to `Collection` yields deterministic iterations.
  internal struct Locals: Hashable, Sendable {

    /// A key/value pair in an abstract context.
    private struct Slot: Hashable, Sendable {

      /// An orderable representation of `key`.
      let rank: Int

      /// The key of the pair.
      let key: IRValue

      /// The value of the pair.
      var value: AbstractValue<Domain>

    }

    /// The contents of the context.
    private var contents: ContiguousArray<Slot> = []

    /// Creates an empty context.
    internal init() {}

    /// Forms a context by merging the contents of `batch`.
    internal init<T: Collection<Self>>(merging batch: T) {
      if let (h, t) = batch.headAndTail {
        self = t.reduce(into: h, { (a, b) in a.merge(b) })
      } else {
        self.init()
      }
    }

    /// Accesses the value at assigned to `key`, which is either a register or a parameter.
    ///
    /// - Complexity: O(log n) where n is the number en key/value pairs in `self`.
    internal subscript(key: IRValue) -> AbstractValue<Domain>? {
      get {
        let r = Self.rank(key)
        let i = contents.partitioningIndex(where: { (s) in s.rank >= r })
        if (i < contents.count) && (contents[i].rank == r) {
          return contents[i].value
        } else {
          return nil
        }
      }
      _modify {
        let r = Self.rank(key)
        let i = contents.partitioningIndex(where: { (s) in s.rank >= r })
        var out: AbstractValue<Domain>?

        // Define a slide for processing the value that will be stored in `out`.
        defer {
          if let o = out {
            if (i < contents.count) && (contents[i].rank == r) {
              contents[i].value = o
            } else {
              contents.insert(.init(rank: r, key: key, value: o), at: i)
            }
          } else if (i < contents.count) && (contents[i].rank == r) {
            contents.remove(at: i)
          }
        }

        // Determine the initial value of `out`.
        if (i < contents.count) && (contents[i].rank == r) {
          out = contents[i].value
        } else {
          out = nil
        }

        yield &out
      }
    }

    /// Merges `other` into `self`.
    internal mutating func merge(_ other: Self) {
      var l = 0
      var r = 0

      while l < self.contents.count {
        if r >= other.contents.count {
          self.contents.removeLast(self.contents.count - l)
          break
        } else if self.contents[l].rank < other.contents[r].rank {
          self.contents.remove(at: l)
        } else if self.contents[l].rank > other.contents[r].rank {
          r += 1
        } else {
          self.contents[l].value = self.contents[l].value && other.contents[r].value
          l += 1
          r += 1
        }
      }
    }

    /// Returns a representation of `v` suitable to sort the internal storage of a context.
    private static func rank(_ v: IRValue) -> Int {
      switch v {
      case .parameter(let i):
        return i | 1 << (Int.bitWidth - 1)
      case .register(let i):
        return i.address.rawValue
      default:
        fatalError("invalid key")
      }
    }

  }

  /// The values assigned to registers and parameters.
  internal var locals: Locals = .init()

  /// The state of memory.
  internal var memory: [AbstractPlace: AbstractObject<Domain>] = [:]

  /// Creates an empty context.
  internal init() {}

  /// Forms a context by merging the contents of `batch`.
  internal init<T: Collection<Self>>(merging batch: T) {
    if let (h, t) = batch.headAndTail {
      self = t.reduce(into: h, { (a, b) in a.merge(b) })
    } else {
      self.init()
    }
  }

  /// Merges `other` into `self`.
  internal mutating func merge(_ other: Self) {
    locals.merge(other.locals)
    memory.merge(other.memory, uniquingKeysWith: &&)
  }

  /// Returns the result calling `action` with a projection of the object at `place`, using `typer`
  /// to compute abstract layouts..
  internal mutating func withObject<T>(
    at place: AbstractPlace, computingLayoutWith typer: inout Typer,
    _ action: (inout AbstractObject<Domain>, inout Typer) -> T
  ) -> T {
    switch place {
    case .root:
      return action(&memory[place]!, &typer)
    case .subplace(let root, let path):
      if path.isEmpty {
        return action(&memory[place]!, &typer)
      } else {
        return modify(&memory[.root(root)]!) { (o) in
          o.withSubobject(at: path, computingLayoutWith: &typer, action)
        }
      }
    }
  }

  /// Sets the value of the object at `place` using `typer` to compute abstract layouts.
  internal mutating func setValue(
    _ value: AbstractObject<Domain>.Value, at place: AbstractPlace,
    computingLayoutWith typer: inout Typer
  ) {
    withObject(at: place, computingLayoutWith: &typer, { (o, _) in o.value = value })
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
    (contents[p].key, contents[p].value)
  }

}

extension AbstractContext: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    let ls = printer.show(locals)
    let ms = memory.sorted(by: \.key).reduce(into: "") { (s, p) in
      s += "\(printer.show(p.key)) ↦ \(printer.show(p.value))\n"
    }

    return """
      locals:
      \(ls.indented)
      memory:
      \(ms.indented)
      """
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

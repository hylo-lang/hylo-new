/// The context needed to demangle a symbol, including the stream being parsed and the lookup
/// tables for strings and symbols.
struct DemanglingContext {

  /// The stream being parsed.
  private var stream: Substring

  /// The list of demangled strings, in order of occurrence (a.k.a. the string lookup table).
  private var strings: [Substring] = []

  /// The list of demangled symbols, in order of occurrence (a.k.a. the symbol lookup table).
  private var symbols: [DemangledSymbol] = []

  /// A helper for printing debugging information during demangling.
  ///
  /// The helper won't print anything unless `debug.enabled` is assigned to `true`.
  private var debug = DebugPrinter(enabled: false)

  /// The characters left to parse.
  var remaining: String {
    String(stream)
  }

  /// `true` iff we demangled everything.
  var isComplete: Bool {
    stream.isEmpty
  }

  /// Creates an instance that parses the contents of `stream`.
  internal init(stream: Substring) {
    self.stream = stream
  }

  /// Consumes and returns a mangling operator iff `stream` starts with one.
  mutating func takeOperator() -> ManglingOperator? {
    guard let r = ManglingOperator(prefixing: stream) else { return nil }
    debug.print("- op: \(r)")
    stream = stream.dropFirst(r.rawValue.count)
    return r
  }

  /// Returns the mangling operator at the start of `stream`, if any, without consuming it.
  func peekOperator() -> ManglingOperator? {
    .init(prefixing: stream)
  }

  /// Consumes and returns and mangled string, returning `nil` iff the data is corrupted.
  mutating func takeString() -> String? {
    guard let length = takeInteger()?.rawValue else { return nil }
    switch length {
    case 0:
      return String(stream[stream.startIndex ..< stream.startIndex])

    case 1:
      guard let n = takeInteger() else { return nil }
      guard n.rawValue < strings.count else {
        debug.print("ERROR: invalid string reference \(n), only \(strings.count) strings demangled so far")
        return nil
      }
      return String(strings[Int(n.rawValue)])

    case let n:
      let j = stream.index(stream.startIndex, offsetBy: Int(n - 2))
      guard j <= stream.endIndex else {
        debug.print("ERROR: out of bounds when reading string")
        return nil
      }
      let r = stream[..<j]
      strings.append(r)
      stream = stream[j...]
      return String(r)
    }
  }

  /// Assuming `stream` starts with a mangled `Int` value, consumes and returns it; returns `nil`
  /// otherwise.
  mutating func takeInt() -> Int? {
    takeInteger().map({ Int(bitPattern: UInt(truncatingIfNeeded: $0.rawValue)) })
  }

  /// Assuming `stream` starts with a mangled `UInt32` value, consumes and returns it; returns `nil`
  /// otherwise.
  mutating func takeUInt32() -> UInt32? {
    takeInteger().map({ UInt32(truncatingIfNeeded: $0.rawValue) })
  }

  /// Assuming `stream` starts with a mangled `UInt64` value, consumes and returns it; returns `nil`
  /// otherwise.
  mutating func takeUInt64() -> UInt64? {
    takeInteger().map({ $0.rawValue })
  }

  /// Assuming `stream` starts with a mangled integer, consumes and returns it; returns `nil`
  /// otherwise.
  private mutating func takeInteger() -> Base64VarUInt? {
    guard let (v, i) = Base64VarUInt.decode(from: stream) else {
      return nil
    }
    stream = stream[i...]
    return v
  }

  /// Assuming `stream` starts with a base 64 digit, consumes and returns it. Returns `nil` iff
  /// data is corrupted.
  mutating func takeBase64Digit() -> Base64Digit? {
    stream.popFirst().flatMap(Base64Digit.init(_:))
  }

  /// Assuming `stream` starts with a mangled `T`, consumes and returns it. Returns `nil` iff
  /// data is corrupted.
  mutating func take<T: RawRepresentable>(_: T.Type) -> T? where T.RawValue == UInt8 {
    takeBase64Digit().flatMap({ (d) in T(rawValue: d.rawValue) })
  }

  /// Demangles a list of `T`s from `stream`, calling `takeItem` to parse each individual element.
  mutating func takeItems<T>(takingEachWith takeItem: (inout Self) -> T?) -> [T]? {
    guard let n = takeInteger() else { return nil }
    var xs: [T] = .init(minimumCapacity: Int(n.rawValue))

    for _ in 0 ..< n.rawValue {
      guard let x = takeItem(&self) else { return nil }
      xs.append(x)
    }
    return xs
  }

  /// Demangles a reserved symbol.
  mutating func takeReserved() -> DemangledSymbol? {
    let r = take(ReservedSymbol.self).map(DemangledSymbol.init(reserved:))
    debug.print("- reading reserved \(r?.description ?? "nil")")
    return r
  }

  /// Demangles a reference to a symbol already seen by `self`.
  mutating func takeLookupReference() -> DemangledSymbol? {
    guard let n = takeInteger() else { return nil }
    guard n.rawValue < symbols.count else {
      debug.print("ERROR: out of bounds when looking up \(n)")
      return nil
    }
    if debug.enabled {
      let s = symbols[Int(n.rawValue)]
      debug.print("- lookup at \(n): \(s) \(s.kind)")
    }
    return symbols[Int(n.rawValue)]
  }

  /// Records that we've seen `s`.
  mutating func record(symbol s: DemangledSymbol) {
    debug.print("- recording \(s.kind) \(s) at \(symbols.count)")
    symbols.append(s)
  }

  /// Returns the application of `action` on a mutable `self`, performing debug logging for reading
  /// an entity.
  mutating func readingEntity<T>(_ action: (_ source: inout Self) -> T) -> T {
    withUnsafeMutablePointer(to: &self) { (me) in
      me.pointee.debug.withScope("read entity") {
        action(&me.pointee)
      }
    }
  }

  /// Returns the application of `action` on a mutable `self`, performing debug logging for reading
  /// a type.
  mutating func readingType<T>(_ action: (_ source: inout Self) -> T) -> T {
    withUnsafeMutablePointer(to: &self) { (me) in
      me.pointee.debug.withScope("read type") {
        action(&me.pointee)
      }
    }
  }

}

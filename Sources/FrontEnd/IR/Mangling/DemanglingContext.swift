/// The context needed to demangle a symbol, including the stream being parsed and the lookup
/// tables for strings and symbols.
struct DemanglingContext {

  // Functions starting with `take` consume the corresponding data from `stream` and return it,
  // returning `nil` if the data is corrupted.

  /// The stream being parsed.
  private var stream: Substring

  /// The list of demangled strings, in order of occurrence (a.k.a. the string lookup table).
  private var strings: [Substring] = []

  /// The list of demangled symbols, in order of occurrence (a.k.a. the symbol lookup table).
  private var symbols: [DemangledSymbol] = []

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
    stream = stream.dropFirst(r.rawValue.count)
    return r
  }

  /// Returns the mangling operator at the start of `stream`, if any, without consuming it.
  func peekOperator() -> ManglingOperator? {
    .init(prefixing: stream)
  }

  /// Consumes and returns a mangled string.
  mutating func takeString() -> String? {
    guard let length = takeInteger()?.rawValue else { return nil }
    switch length {
    case 0:
      return String(stream[stream.startIndex ..< stream.startIndex])

    case 1:
      guard let n = takeInteger() else { return nil }
      guard n.rawValue < strings.count else { return nil }
      return String(strings[Int(n.rawValue)])

    case let n:
      guard let j = stream.index(stream.startIndex, offsetBy: Int(n - 2), limitedBy: stream.endIndex) else { return nil }
      let r = stream[..<j]
      strings.append(r)
      stream = stream[j...]
      return String(r)
    }
  }

  /// Consumes and returns a mangled `Int` value.
  mutating func takeInt() -> Int? {
    takeInteger().map({ Int(bitPattern: UInt(truncatingIfNeeded: $0.rawValue)) })
  }

  /// Consumes and returns a mangled `UInt32` value.
  mutating func takeUInt32() -> UInt32? {
    takeInteger().map({ UInt32(truncatingIfNeeded: $0.rawValue) })
  }

  /// Consumes and returns a mangled `UInt64` value.
  mutating func takeUInt64() -> UInt64? {
    takeInteger().map({ $0.rawValue })
  }

  /// Consumes and returns a mangled integer.
  private mutating func takeInteger() -> Base64VarUInt? {
    guard let (v, i) = Base64VarUInt.decode(from: stream) else {
      return nil
    }
    stream = stream[i...]
    return v
  }

  /// Consumes and returns a mangled base-64 digit value.
  mutating func takeBase64Digit() -> Base64Digit? {
    stream.popFirst().flatMap(Base64Digit.init(_:))
  }

  /// Consumes and returns a mangled `T` value.
  mutating func take<T: RawRepresentable>(_: T.Type) -> T? where T.RawValue == UInt8 {
    takeBase64Digit().flatMap({ (d) in T(rawValue: d.rawValue) })
  }

  /// Consumes and returns a list of mangled `T` values, calling `takeItem` to parse each
  /// individual element.
  mutating func takeItems<T>(takingEachWith takeItem: (inout Self) -> T?) -> [T]? {
    guard let n = takeInteger() else { return nil }
    var xs: [T] = .init(minimumCapacity: Int(n.rawValue))

    for _ in 0 ..< n.rawValue {
      guard let x = takeItem(&self) else { return nil }
      xs.append(x)
    }
    return xs
  }

  /// Consumes and returns a mangled reserved symbol.
  mutating func takeReserved() -> DemangledSymbol? {
    take(ReservedSymbol.self).map(DemangledSymbol.init(reserved:))
  }

  /// Consumes and returns a reference to a symbol already seen by `self`.
  mutating func takeLookupReference() -> DemangledSymbol? {
    if let n = takeInteger(), n.rawValue < symbols.count {
        return symbols[Int(n.rawValue)]
    } else {
        return nil
    }
  }

  /// Records that we've seen `s`.
  mutating func record(symbol s: DemangledSymbol) {
    symbols.append(s)
  }

}

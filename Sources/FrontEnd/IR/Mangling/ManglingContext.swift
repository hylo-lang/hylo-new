/// The context for mangling a symbol.
///
/// It maintains the state of the mangling process, including the output being built, as well as
/// the lookup tables and current qualification.
struct ManglingContext {

  /// The mangled string being built.
  internal private(set) var output: String

  /// A table mapping mangled strings to their position in the string lookup table.
  private var stringPosition: [String: Int] = [:]

  /// A table mapping mangled symbols to their position in the symbol lookup table.
  private var symbolPosition: [MangledSymbol: Int] = [:]

  /// The innermost scope being mangled, if any.
  private var qualification: ScopeIdentity?

  /// A table mapping known symbols to their reserved mangled identifier.
  private var reserved: [MangledSymbol: ReservedSymbol] = [:]

  /// Creates an instance for mangling symbols in `program`.
  init(_ program: Program) {
    output = ""
    initializeReservedSymbols(program: program)
  }

  /// Initializes the table of reserved symbols.
  private mutating func initializeReservedSymbols(program: Program) {
    var types = program.types
    reserved[.type(AnyTypeIdentity(types.never()))] = .never
    reserved[.type(.void)] = .void
    if program.containsStandardLibrary {
      let stdlib = program.modules.values.first(where: { (m) in m.isStandardLibrary })!
      reserved[.module(stdlib.identity)] = .hylo
      registerStandardLibraryDeclaration(.bool, as: .bool, in: program)
      registerStandardLibraryDeclaration(.int, as: .int, in: program)
      registerStandardLibraryDeclaration(.int64, as: .int64, in: program)
    }
  }

  /// Extends `self.reserved` to associate the declaration of `d` to the reserved symbol `s`.
  private mutating func registerStandardLibraryDeclaration(
    _ d: Program.StandardLibraryEntity, as s: ReservedSymbol, in program: Program
  ) {
    reserved[.node(AnySyntaxIdentity(program.standardLibraryDeclaration(d)))] = s
  }

  /// Writes `x` to `self.output`.
  private mutating func add<T: TextOutputStreamable>(_ x: T) {
    x.write(to: &output)
  }

  /// Writes `string` to `output`, prefixed by its length encoded as a variable-length integer.
  mutating func add<T: StringProtocol>(string: T) {
    let s = String(string)

    if s.isEmpty {
      add(integer: 0)
    } else if let n = stringPosition[s] {
      add(integer: 1)
      add(integer: n)
    } else {
      add(integer: s.count + 2)
      add(string)
      stringPosition[s] = stringPosition.count
    }
  }

  /// Writes `v` encoded as a variable-length integer to `output`.
  mutating func add(integer v: Int) {
    Base64VarUInt(UInt(bitPattern: v)).write(to: &output)
  }

  /// Writes `v` encoded as a variable-length integer to `output`.
  mutating func add(integer v: UInt32) {
    Base64VarUInt(UInt64(v)).write(to: &output)
  }

  /// Writes `v` encoded as a variable-length integer to `output`.
  mutating func add(integer v: UInt64) {
    Base64VarUInt(v).write(to: &output)
  }

  /// Writes the raw value of `v` encoded as a base 64 digit to `output`.
  mutating func add<T: RawRepresentable<UInt8>>(base64Digit v: T) {
    add(base64Digit: v.rawValue)
  }

  /// Writes `v` encoded as a base 64 digit to `output`.
  mutating func add(base64Digit v: UInt8) {
    add(Base64Digit(rawValue: v)!.description)
  }

  /// Writes `o` to `output`.
  mutating func add(operator o: ManglingOperator) {
    o.write(to: &output)
  }

  /// Writes the mangled representation of `items` to `output`, calling `addItem` to mangle each
  /// individual element.
  mutating func add<T: Collection>(
    items: T,
    appendingEachWith addItem: (inout Self, T.Element) -> Void
  ) {
    add(integer: items.count)
    for i in items {
      addItem(&self, i)
    }
  }

  /// Records `s` in the symbol lookup table if it is not reserved or already recorded.
  mutating func record(symbol s: MangledSymbol, in program: Program) {
    if symbolPosition.keys.contains(s) || reserved.keys.contains(s) { return }
    symbolPosition[s] = symbolPosition.count
  }

  /// Records `q` as the innermost scope being mangled, and returns the previous recorded value.
  mutating func record(qualification q: ScopeIdentity?) -> ScopeIdentity? {
    let previous = qualification
    qualification = q
    return previous
  }

  /// If `s` is reserved or has already been inserted in the symbol lookup table, writes a lookup
  /// reference to it and returns `true`. Otherwise, returns `false` without modifying `self`.
  mutating func addIf(reservedOrRecorded s: MangledSymbol, in program: Program) -> Bool {
    addIf(reserved: s) || addIf(recorded: s, in: program)
  }

  /// Writes a lookup reference to `s` and returns `true` iff `s` is a reserved mangling symbol.
  // Otherwise, returns `false` without modifying `self`.
  private mutating func addIf(reserved s: MangledSymbol) -> Bool {
    if let r = reserved[s] {
      if case .type = s {
        add(operator: .reservedType)
      } else {
        add(operator: .reserved)
      }
      r.write(to: &output)
      return true
    } else {
      return false
    }
  }

  /// Writes a lookup reference to `s` and returns `true` iff `s` is in the lookup table.
  /// Otherwise, returns `false` without modifying `self`.
  private mutating func addIf(recorded s: MangledSymbol, in program: Program) -> Bool {
    if let p = symbolPosition[s] {
      if case .type = s {
        add(operator: .lookupType)
      } else {
        add(operator: .lookup)
      }
      add(integer: p)
      return true
    } else {
      return false
    }
  }

  /// If `q` is the qualification accumulated so far, writes a lookup reference to it and returns
  /// `true`. Otherwise, returns `false` without modifying `self`.
  mutating func addIf(qualification q: ScopeIdentity) -> Bool {
    if q == qualification {
      add(operator: .lookupRelative)
      return true
    } else {
      return false
    }
  }

}

/// The context for mangling a symbol, type, or scope.
/// It maintains the state of the mangling process, including the output being built, as well as
/// the lookup tables and current qualification.
struct ManglingContext {

  /// The mangled string being built.
  public private(set) var output: String

  /// A table mapping mangled strings to their position in the string lookup table.
  private var stringPosition: [String: Int] = [:]

  /// A table mapping mangled symbols to their position in the symbol lookup table.
  private var symbolPosition: [ManglingSymbol: Int] = [:]

  /// The innermost scope being mangled, if any.
  private var qualification: ScopeIdentity?

  /// A table mapping known symbols to their reserved mangled identifier.
  private var reserved: [ManglingSymbol: ReservedSymbol] = [:]

  /// Object used for printing debugging information during mangling.
  /// Set `enabled` to `true` to enable debug printing.
  private var debug = DebugPrinter(enabled: false)

  /// An instance for mangling symbols in `program`.
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
    _ d: Program.StandardLibraryEntity, as s: ReservedSymbol,
    in program: Program
  ) {
    reserved[.node(AnySyntaxIdentity(program.standardLibraryDeclaration(d)))] = s
  }

  /// Writes `x` to `output`.
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
    debug.print("- op: \(o)")
  }

  /// Writes the mangled representation of `items`, calling `addItem` to mangle each individual
  /// element to `output`.
  mutating func add<T: Collection>(
    items: T,
    appendingEachWith addItem: (T.Element, inout Self) -> Void
  ) {
    add(integer: items.count)
    for i in items {
      addItem(i, &self)
    }
  }

  /// Records `s` in the symbol lookup table if it is not reserved or already recorded.
  mutating func record(symbol s: ManglingSymbol, in program: Program) {
    if symbolPosition.keys.contains(s) || reserved.keys.contains(s) { return }
    debug.print("- recording \(Self.debugName(symbol: s, in: program)): \(symbolPosition.count)")
    symbolPosition[s] = symbolPosition.count
  }

  /// Records `q` as the innermost scope being mangled, and returns the previous one.
  mutating func record(qualification q: ScopeIdentity?) -> ScopeIdentity? {
    let previous = qualification
    qualification = q
    return previous
  }

  /// If `s` is reserved or has already been inserted in the symbol lookup table, writes a lookup
  /// reference to it and returns `true`. Otherwise, returns `false`.
  mutating func appendIf(reservedOrRecorded s: ManglingSymbol, in program: Program) -> Bool {
    appendIf(reserved: s) || appendIf(recorded: s, in: program)
  }

  /// Writes a lookup reference to `s` and returns `true` iff `s` is a reserved
  /// mangling symbol. Otherwise, returns `false` without modifying `self`.
  private mutating func appendIf(reserved s: ManglingSymbol) -> Bool {
    if let r = reserved[s] {
      if case .type = s {
        add(operator: .reservedType)
      } else {
        add(operator: .reserved)
      }
      r.write(to: &output)
      debug.print("- writing reserved \(s)")
      return true
    } else {
      return false
    }
  }

  /// Writes a lookup reference to `s` and returns `true` iff `s` in the lookup table. Otherwise,
  /// returns `false` without modifying `self`.
  private mutating func appendIf(recorded s: ManglingSymbol, in program: Program) -> Bool {
    if let p = symbolPosition[s] {
      if case .type = s {
        add(operator: .lookupType)
      } else {
        add(operator: .lookup)
      }
      add(integer: p)
      debug.print("- lookup at \(p): \(Self.debugName(symbol: s, in: program))")
      return true
    } else {
      return false
    }
  }

  /// If `q` is the qualification accumulated so far, writes a lookup reference to it and returns
  /// `true`. Otherwise, returns `false`.
  mutating func appendIf(qualification q: ScopeIdentity) -> Bool {
    if q == qualification {
      add(operator: .lookupRelative)
      return true
    } else {
      return false
    }
  }

  /// Executes `action` on a mutable `self`, performing debug logging for `d` in `program`.
  mutating func writing(
    decl d: DeclarationIdentity, program: Program, _ action: (_ source: inout Self) -> Void
  ) {
    withUnsafeMutablePointer(to: &self) { (me) in
      me.pointee.debug.withScope("write decl: \(program.debugName(of: d))") {
        action(&me.pointee)
      }
    }
  }

  /// Executes `action` on a mutable `self`, performing debug logging for the qualification.
  mutating func writingQualification(
    _ action: (_ source: inout Self) -> Void
  ) {
    withUnsafeMutablePointer(to: &self) { (me) in
      me.pointee.debug.withScope("write qualification") {
        action(&me.pointee)
      }
    }
  }

  /// Executes `action` on a mutable `self`, performing debug logging for `t` in `program`.
  mutating func writing(
    type t: AnyTypeIdentity, program: Program, _ action: (_ source: inout Self) -> Void
  ) {
    withUnsafeMutablePointer(to: &self) { (me) in
      me.pointee.debug.withScope("write type: \(Self.debugName(of: t, in: program))") {
        action(&me.pointee)
      }
    }
  }

  /// Returns the name of `t` in `program` for debug printing purposes.
  private static func debugName(of t: AnyTypeIdentity, in program: Program) -> String {
    var printer = TreePrinter(program: program)
    return printer.show(t)
  }

  /// Returns the name of `s` in `program` for debug printing purposes.
  private static func debugName(symbol s: ManglingSymbol, in program: Program) -> String {
    switch s {
    case .type(let x):
      return "type \(debugName(of: x, in: program))"
    case .node(let x):
      let n = program.name(of: DeclarationIdentity(uncheckedFrom: x))
      return "entity \(n?.description ?? "scope?")"
    case .fileScope(let x):
      return "scope entity \(x.file)"
    case .module:
      return "module"
    }
  }

}

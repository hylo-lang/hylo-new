extension SourceFile {

  /// The identity of a source file added to a module.
  public struct ID: Comparable, Hashable, RawRepresentable, Showable, Sendable {

    /// The raw value of this identity.
    public let rawValue: UInt32

    /// Creates an instance from its raw value.
    public init(rawValue: UInt32) {
      self.rawValue = rawValue
    }

    /// Creates an instance identifying the file at offset `f` in module `m`.
    public init(module m: Module.ID, offset f: Int) {
      precondition(m < (1 << 16))
      precondition(f < (1 << 16))
      self.rawValue = UInt32(m & 0xffff) + (UInt32(f & 0xffff) << 16)
    }

    /// Creates an instance identifying the file containing `n`.
    public init<T: SyntaxIdentity>(containing n: T) {
      self.rawValue = UInt32(truncatingIfNeeded: n.erased.bits)
    }

    /// The module offset of the node represented by `self` in its containing collection.
    public var module: Module.ID {
      .init(rawValue & 0xffff)
    }

    /// The file offset of the node represented by `self` in its containing collection.
    public var offset: Int {
      .init((rawValue & 0xffff0000) >> 16)
    }

    /// Returns the contents of `self`.
    public func show(using printer: inout TreePrinter) -> String {
      printer.program[self].source.text
    }

    /// Returns `true` iff `l` is ordered before `r` when iterating over the sources of a module.
    public static func < (l: Self, r: Self) -> Bool {
      l.rawValue < r.rawValue
    }

  }

}

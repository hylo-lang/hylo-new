import Foundation

/// Returns the Hylo source code declaring the standard library's integer types.
internal func generateIntegerTypes() -> String {
  var types: [IntegerTypeDefinition] = []

  for bits in [8, 16, 32, 64] {
    types.append(.fixedSize(bits: bits, .signed, includedConformances: .minimal))
    types.append(.fixedSize(bits: bits, .unsigned, includedConformances: .minimal))
  }

  types.append(
    .init(
      name: "Int",
      documentation:
        "/// A signed integer type that can represent any object size on the target platform.",
      builtinType: "word", .signed, .fittingLargestObjectSize, includedConformances: .all))

  types.append(
    .init(
      name: "UInt",
      documentation:
        "/// An unsigned integer type that can represent any object size on the target platform.",
      builtinType: "word", .unsigned, .fittingLargestObjectSize, includedConformances: .minimal))

  return types.map(\.description).joined(separator: "\n")
}

extension IntegerTypeDefinition {

  /// Creates a fixed-size integer type's definition.
  static func fixedSize(
    bits: Int, _ signedness: Signedness, includedConformances: Conformances
  ) -> IntegerTypeDefinition {
    .init(
      name: signedness == .signed ? "Int\(bits)" : "UInt\(bits)",
      documentation: "/// \(prefixed(bits))-bit \(signedness) integer.",
      builtinType: "i\(bits)", signedness, .fixedWidth(bits: bits),
      includedConformances: includedConformances)
  }

}

/// Returns `x` prefixed with an indefinite article.
private func prefixed(_ x: Int) -> String {
  x.description.first == "8" ? "An \(x)" : "A \(x)"
}

/// Whether an integer type is signed or unsigned.
private enum Signedness: String, CustomStringConvertible {

  case signed = "s"
  case unsigned = "u"

  /// The description of the signedness.
  var description: String {
    switch self {
    case .signed: "signed"
    case .unsigned: "unsigned"
    }
  }

  /// The abbreviation used in builtin type names.
  var abbreviated: String { rawValue }

}

/// The size of an integer type.
private enum Size: Equatable {

  /// The type can represent the size of the largest object in memory on the target platform.
  ///
  /// Equivalent of `size_t`/`ssize_t` in C.
  case fittingLargestObjectSize

  /// The type has exactly `bits` bits.
  case fixedWidth(bits: Int)

}

/// The set of conformances to generate for an integer type.
private enum Conformances {

  /// Provide all conformances.
  case all

  /// Provide only `Movable` and `ExpressibleByIntegerLiteral`.
  case minimal

}

/// Information for emitting a standard library integer type.
private struct IntegerTypeDefinition: CustomStringConvertible {

  /// The exposed name of the generated declaration, e.g., `Int64`.
  let declarationName: String

  /// The documentation of the type, including `///` prefixes.
  let declarationDocumentation: String

  /// The name of the stored underlying builtin type, e.g., `i64`.
  let builtinType: String

  /// Whether the integer is signed.
  let signedness: Signedness

  /// The size of the type.
  let size: Size

  /// The set of conformances to generate.
  let includedConformances: Conformances

  /// Constructs an instance from its parts.
  init(
    name: String, documentation: String,
    builtinType: String, _ signedness: Signedness, _ size: Size,
    includedConformances: Conformances
  ) {
    self.declarationName = name
    self.declarationDocumentation = documentation
    self.builtinType = builtinType
    self.signedness = signedness
    self.size = size
    self.includedConformances = includedConformances
  }

  /// The code introducing the `abs()` method for signed types, nil otherwise.
  var absMethod: String? {
    signedness == .unsigned
      ? nil
      : """


        /// Returns the absolute value of `self`.
        ///
        /// - Requires: `self` must not be `\(declarationName)`'s minimum value.
        @inline(always)
        public fun abs() -> Self {
          if self < Self.zero() { Self.zero() - self } else { Self(value: self.value) }
        }
      """
  }

  /// An expression denoting the bit pattern of the receiver with each bit inversed.
  ///
  /// The result of the expression is an instance of the type described by `Self`.
  var inversed: String {
    ".new(value: Builtin.xor_\(builtinType)(self.value, (-1 as Self).value))"
  }

  /// An expression denoting the smallest instance of the type that `Self` describes.
  ///
  /// The result of the expression is an instance of the type described by `Self`.
  var minimumValue: String {
    // Trivial if the type is unsigned.
    if signedness == .unsigned { return "0" }

    // Otherwise, the result depends on the bit width.
    switch size {
    case .fixedWidth(let bits):
      return "\(-(Int128(1) << (bits - 1))) as Self"

    case .fittingLargestObjectSize:
      let x = "Builtin.lshr_\(builtinType)((-1 as Self).value, (1 as Self).value)"
      let y = "Builtin.xor_\(builtinType)(\(x), (-1 as Self).value)"
      return "Self.new(value: \(y))"
    }
  }

  /// An expression denoting the largest instance of the type that `Self` describes.
  ///
  /// The result of the expression is an instance of the type described by `Self`.
  var maximumValue: String {
    if signedness == .signed {
      let x = "Builtin.lshr_\(builtinType)((-1 as Self).value, (1 as Self).value)"
      return "Self.new(value: \(x))"
    } else {
      let s = String(declarationName.dropFirst())
      return "Self.new(value: (-1 as \(s)).value)"
    }
  }

  /// An expression denoting the number of bits in the representation of an instance of the type
  /// that `Self` describes.
  ///
  /// The result of the expression is an instance of `Hylo.Int`.
  var bitWidth: String {
    switch size {
    case .fittingLargestObjectSize:
      "Int(value: Builtin.ctlz_word(0.value))"
    case .fixedWidth(let bits):
      String(describing: bits)
    }
  }

  /// The body of `infix>>(_:)`, which shifts the bit representation to the right.
  var shiftRight: String {
    if signedness == .signed {
      """
      if other >= Self.bit_width() {
            if self < Self.zero() { (-1 as Self) } else { Self.zero() }
          } else if other >= 0 {
            Self.new(value: Builtin.ashr_\(builtinType)(self.value, Self(other).value))
          } else if (0 - other) < Self.bit_width() {
            Self.new(value: Builtin.shl_\(builtinType)(self.value, Self(0 - other).value))
          } else {
            Self.zero()
          }
      """
    } else {
      """
      if other >= Self.bit_width() {
            Self.zero()
          } else if other >= 0 {
            Self.new(value: Builtin.lshr_\(builtinType)(self.value, Self(other).value))
          } else if (0 - other) < Self.bit_width() {
            Self.new(value: Builtin.shl_\(builtinType)(self.value, Self(0 - other).value))
          } else {
            Self.zero()
          }
      """
    }
  }

  /// The body of `init(_:)`, which converts instances of `Hylo.Int`.
  var initializeFromInt: String {
    if signedness == .signed {
      initializeSignedFromInt
    } else {
      initializeUnsignedFromInt
    }
  }

  /// The body of an `init(_:)`, which converts instances of `Hylo.Int`, assuming `Self` describes
  /// a signed type.
  var initializeSignedFromInt: String {
    if builtinType == "word" {
      """
      &self = Self(value: other.value)
      """
    } else {
      """
      let source_width = Int.bit_width()
          let target_width = Self.bit_width()
          let n = if other < 0 { ~other } else { other + 0 }
          let d = Int(
            value: Builtin.sub_word(
              source_width.value,
              Builtin.ctlz_word(Builtin.shl_word(n.value, 1.value))))
          if d > target_width { Builtin.trap() }
          &self = Self(value: Builtin.trunc_or_sext_word_\(builtinType)(other.value))
      """
    }
  }

  /// The body of an `init(_:)`, which converts instances of `Hylo.Int`, assuming `Self` describes
  /// an unsigned type.
  var initializeUnsignedFromInt: String {
    if builtinType == "word" {
      """
      if other < 0 { Builtin.trap() }
          &self = Self(value: other.value)
      """
    } else {
      """
      if other < 0 { Builtin.trap() }
          let source_width = Int.bit_width()
          let target_width = Self.bit_width()
          let d = Int(
            value: Builtin.sub_word(
              source_width.value,
              Builtin.ctlz_word(Builtin.shl_word(other.value, 1.value))))
          if d > target_width { Builtin.trap() }
          &self = Self(value: Builtin.trunc_or_zext_word_\(builtinType)(other.value))
      """
    }
  }

  /// Returns an expression denoting the value of `n`, which is an instance of `builtinType`, as an
  /// instance of `Builtin.word`.
  ///
  /// - Requires: The value denoted by `n` is representable as an instance of `Builtin.word`.
  func asInstanceOfWord(_ n: String) -> String {
    if builtinType == "word" {
      n
    } else if signedness == .signed {
      "Builtin.trunc_or_sext_\(builtinType)_word(\(n))"
    } else {
      "Builtin.trunc_or_zext_\(builtinType)_word(\(n))"
    }
  }

  /// The source code representation of this type.
  var description: String {
    """
    \(declarationDocumentation)
    @_symbol(\"\(declarationName)\")
    public struct \(declarationName) is Deinitializable {

      /// The raw value of this instance.
      module var value: Builtin.\(builtinType)

      /// Creates an instance with its raw value.
      @inline(always)
      module memberwise init

      /// Creates an instance with value `0`.
      @inline(always)
      public init() {
        &self.value = Builtin.zeroinitializer_\(builtinType)()
      }

      /// Creates an instance whose value is the same as that of `other`.
      ///
      /// - Requires: the value of `other` is representable as an instance of `Self`.
      @inline(always)
      public init(other: Int) {
        \(initializeFromInt)
      }\(absMethod ?? "")

      /// Returns the number of bits that are set in the representation of `self`.
      @inline(always)
      public fun nonzero_bit_count() -> Int {
        Int(value: \(asInstanceOfWord("Builtin.ctpop_\(builtinType)(self.value)")))
      }

      /// Returns the number of leading zeros in the representation of `self`.
      @inline(always)
      public fun leading_zero_bit_count() -> Int {
        Int(value: \(asInstanceOfWord("Builtin.ctlz_\(builtinType)(self.value)")))
      }

      /// Returns the number of trailing zeros in the representation of `self`.
      @inline(always)
      public fun trailing_zero_bit_count() -> Int {
        Int(value: \(asInstanceOfWord("Builtin.cttz_\(builtinType)(self.value)")))
      }

      @inline(always)
      public static fun min() -> Self {
        \(minimumValue)
      }

      @inline(always)
      public static fun max() -> Self {
        \(maximumValue)
      }

      /// Returns the number of bits in the representation of an instance of `Self`.
      @inline(always)
      public static fun bit_width() -> Int {
        \(bitWidth)
      }

      /// Returns `self` with the bits of its representation inversed.
      @inline(always)
      public fun prefix~ () -> Self {
        \(inversed)
      }

      /// Returns the result of performing a bitwise AND operation on `self` and `other`.
      @inline(always)
      public fun infix& (other: Self) -> Self {
        .new(value: Builtin.and_\(builtinType)(self.value, other.value))
      }

      /// Returns the result of performing a bitwise OR operation on `self` and `other`.
      @inline(always)
      public fun infix| (other: Self) -> Self {
        .new(value: Builtin.or_\(builtinType)(self.value, other.value))
      }

      /// Returns the result of performing a bitwise XOR operation on `self` and `other`.
      @inline(always)
      public fun infix^ (other: Self) -> Self {
        .new(value: Builtin.xor_\(builtinType)(self.value, other.value))
      }

      /// Returns the result of shifting `self`'s representation `other` digits to the left.
      ///
      /// If `other` is non-negative, each bit in the representation of `self` is moved by `other`
      /// positions to the left, inserting zeros to the right and discarding any bit ending up at a
      /// position greater than that of the most significant bit.
      ///
      /// If `other` is negative, the result is the same as `self >> other.abs()`.
      @inline(always)
      public fun infix<< (other: Int) -> Self {
        if other >= Self.bit_width() {
          Self.new()
        } else if other >= 0 {
          Self.new(value: Builtin.shl_\(builtinType)(self.value, Self(other).value))
        } else {
          self >> (0 - other)
        }
      }

      /// Returns the result of shifting `self`'s representation `other` digits to the right while
      /// preserving signedness.
      ///
      /// If `other` is non-negative, each bit in the representation of `self` is moved by `other`
      /// positions to the right, inserting copies of the most significant bit to the left and
      /// discarding any bit ending at a negative position.
      ///
      /// If `other` is negative, the result is the same as `self << other.abs()`.
      @inline(always)
      public fun infix>> (other: Int) -> Self {
        \(shiftRight)
      }

      // MARK: Equatable conformance

      /// Returns `true` iff `self` is equal to `other`.
      @inline(always)
      public fun infix== (other: Self) -> Bool {
        .new(value: Builtin.icmp_eq_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is not equal to `other`.
      @inline(always)
      public fun infix!= (other: Self) -> Bool {
        .new(value: Builtin.icmp_ne_\(builtinType)(self.value, other.value))
      }

      // MARK: Comparable conformance

      /// Returns `true` iff `self` is less than `other`.
      @inline(always)
      public fun infix< (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)lt_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is less than or equal to `other`.
      @inline(always)
      public fun infix<= (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)le_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is greater than `other`.
      @inline(always)
      public fun infix> (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)gt_\(builtinType)(self.value, other.value))
      }

      /// Returns `true` iff `self` is greater than or equal to `other`.
      @inline(always)
      public fun infix>= (other: Self) -> Bool {
        .new(value: \
    Builtin.icmp_\(signedness.abbreviated)ge_\(builtinType)(self.value, other.value))
      }

      // MARK: AdditiveArithmetic conformance

      /// Returns `self` added to `other`.
      @inline(always)
      public fun infix+ (other: Self) -> Self {
        let (result, overflow) = \
    Builtin.\(signedness.abbreviated)add_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          Builtin.trap()
        } else {
          return .new(value: result)
        }
      }

      /// Increments `self` by `other`.
      @inline(always)
      public fun infix+= (other: Self) inout {
        &self.value = (self + other).value // Avoid requiring `Movable` or `Copyable`.
      }

      /// Returns `other` subtracted from `self`.
      @inline(always)
      public fun infix- (other: Self) -> Self {
        let (result, overflow) = \
    Builtin.\(signedness.abbreviated)sub_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          Builtin.trap()
        } else {
          return .new(value: result)
        }
      }

      /// Decrements `self` by `other`.
      @inline(always)
      public fun infix-= (other: Self) inout {
        &self.value = (self - other).value // Avoid requiring `Movable` or `Copyable`.
      }

      /// Returns `0`.
      @inline(always)
      public static fun zero() -> Self {
        .new()
      }

      // MARK: Numeric conformance

      /// Returns `self` multiplied by `other`.
      @inline(always)
      public fun infix* (other: Self) -> Self {
        let (result, overflow) = \
    Builtin.\(signedness.abbreviated)mul_with_overflow_\(builtinType)(self.value, other.value)
        if Bool(value: overflow) {
          Builtin.trap()
        } else {
          return .new(value: result)
        }
      }

      /// Multiplies `self` by `other`.
      @inline(always)
      public fun infix*= (other: Self) inout {
        &self.value = (self * other).value // Avoid requiring `Movable` or `Copyable`.
      }

      /// Returns `self` divided by `other`, rounded towards zero.
      ///
      /// - Requires: `other` is not `0`, and the result is representable without overflow.
      @inline(always)
      public fun infix/ (other: Self) -> Self {
        if \(illegalDivision("self", by: "other")) {
          Builtin.trap()
        } else {
          return .new(value: \
    Builtin.\(signedness.abbreviated)div_\(builtinType)(self.value, other.value))
        }
      }\(copyDefinition ?? "")

    }\(conformances)

    """
  }

  /// Returns an expression that's `true` if the result of dividing `x` by `d` results in a value
  /// that is not representable as an instance of `Self`.
  func illegalDivision(_ x: String, by d: String) -> String {
    switch signedness {
    case .signed:
      "\(d) == Self.new() || (\(x) == Self.min() && \(d) == (-1 as Self))"
    case .unsigned:
      "\(d) == Self.new()"
    }
  }

  /// The conformance declarations related to `self`.
  private var conformances: String {
    let minimal =
      """


      public given \(declarationName) is ExpressibleByIntegerLiteral { /* built-in */ }

      public given \(declarationName) is Movable {}
      """

    return switch includedConformances {
    case .all:
      """
      \(minimal)

      public given \(declarationName) is Copyable {}

      public given \(declarationName) is Equatable {}

      public given \(declarationName) is Comparable {}

      public given \(declarationName) is AdditiveArithmetic {}

      public given \(declarationName) is Numeric {}
      """
    case .minimal:
      minimal
    }

  }

  /// The definition of the `copy() -> Self` method, unless synthesized.
  var copyDefinition: String? {
    switch includedConformances {
    case .all:
      nil
    default:
      """


        /// MARK: Copyable conformance (only needed for dummies, synthesized otherwise)

        /// Returns a copy of `self`.
        @inline(always)
        public fun copy() -> Self {
          self + .zero()
        }
      """
    }
  }

}

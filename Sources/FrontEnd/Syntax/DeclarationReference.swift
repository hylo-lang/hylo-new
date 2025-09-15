import Archivist

/// The way in which an entity is referred to.
@Archivable
public enum DeclarationReference: Hashable, Sendable {

  /// A reference to a built-in entity.
  case builtin(BuiltinEntity)

  /// A direct reference.
  case direct(DeclarationIdentity)

  /// A reference to a member declaration that is bound to a receiver.
  ///
  /// The reference was formed from an expression `x.m` where `m` is a non-static member of `x`'s
  /// type. The whole expression denotes a function or subscript partially applied to `x`
  case member(DeclarationIdentity)

  /// A reference to a non-static member inherited by conformance or extension.
  ///
  /// The reference was formed from an expression `x.member` where `member` refers to a symbol
  /// declared in an extension of `x`'s type, or defined as a requirement of a trait to which the
  /// type of `x` conforms.
  ///
  /// In either case, the first value in the payload is an expression computing a record containing
  /// the `member`s implementation (e.g., a conformance witness), the second value is the identity
  /// of the `member`'s declaration, and the last value is a flag indicating whether `member` is
  /// used statically.
  case inherited(WitnessExpression, DeclarationIdentity, statically: Bool)

  /// A reference to a synthetic implementation of a trait requirement.
  case synthetic(DeclarationIdentity)

  /// `true` iff this referennce mentions open variable.
  public var hasVariable: Bool {
    switch self {
    case .builtin, .direct, .member, .synthetic:
      return false
    case .inherited(let w, _, _):
      return w.hasVariable
    }
  }

  /// Returns `true` iff `self` refers to a built-in type operator.
  public var targetIsTypeOperator: Bool {
    switch self {
    case .builtin(.product), .builtin(.sum):
      return true
    default:
      return false
    }
  }

  /// The referred declaration, unless it is built-in.
  public var target: DeclarationIdentity? {
    switch self {
    case .direct(let d), .member(let d), .inherited(_, let d, _):
      return d
    case .builtin, .synthetic:
      return nil
    }
  }

  /// A measure of the complexity of reference's elaborated expression.
  public var elaborationCost: Int {
    switch self {
    case .builtin, .direct, .member, .synthetic:
      return 1
    case .inherited(let w, _, _):
      return 1 + w.elaborationCost
    }
  }

  /// Returns a copy of `self` in which occurrences of `m` have been substituted for `n`.
  internal func substituting(_ m: ExpressionIdentity, for n: ExpressionIdentity) -> Self {
    if case .inherited(let w, let d, let s) = self {
      return .inherited(w.substituting(m, for: n), d, statically: s)
    } else {
      return self
    }
  }

}

extension DeclarationReference: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .builtin(let e):
      return "$<builtin \(e)>"
    case .synthetic(let d):
      return "$<synthetic implementation of \(printer.program.nameOrTag(of: d))>"
    case .direct(let d), .member(let d), .inherited(_, let d, _):
      return printer.program.nameOrTag(of: d)
    }
  }

}

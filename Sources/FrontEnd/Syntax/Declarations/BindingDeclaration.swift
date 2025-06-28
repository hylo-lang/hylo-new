import Archivist

/// The declaration of a (possibly empty) set of bindings.
@Archivable
public struct BindingDeclaration: ModifiableDeclaration {

  /// The grammatical role a binding declaration plays.
  @Archivable
  public enum Role: Hashable, Sendable {

    /// The declaration is used to introduce new bindings unconditionally.
    case unconditional

    /// The declaration is used to receive a value from the implicit context.
    case using

    /// The declaration is used to introduce a value in the implicit context.
    case given

    /// The declaration is used to introduce new bindings iff its pattern matches the value of its
    /// initializer, which is not `nil`.
    case condition

  }

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The grammatical role of this declaration.
  public let role: Role

  /// A pattern introducing the declared bindings.
  public let pattern: BindingPattern.ID

  /// The initializer of the declaration, if any.
  public let initializer: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    modifiers: [Parsed<DeclarationModifier>],
    role: Role,
    pattern: BindingPattern.ID,
    initializer: ExpressionIdentity?,
    site: SourceSpan
  ) {
    self.modifiers = modifiers
    self.role = role
    self.pattern = pattern
    self.initializer = initializer
    self.site = site
  }

  /// `true` iff `self` introduces values into the implicit context.
  public var isImplicit: Bool {
    (role == .using) || (role == .given)
  }

}

extension BindingDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    if role == .given {
      result.append("given ")
    }

    result.append(printer.show(pattern))

    if let i = initializer {
      result.append(" = \(printer.show(i))")
    }

    return result
  }

}

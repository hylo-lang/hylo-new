import Archivist
import Utilities

/// The declaration of a function.
@Archivable
public struct FunctionDeclaration: RoutineDeclaration, Annotatable, Scope {

  /// The introducer of a function declaration.
  @Archivable
  public enum Introducer: UInt8, Sendable {

    /// The function introducer, `fun`.
    case fun

    /// The initializer introducer, `init`.
    case `init`

    /// The memberwise initializer introducer, `memberwise init`
    case memberwiseinit

  }

  /// The annotations on this declaration.
  public let annotations: [Annotation]

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Parsed<Introducer>

  /// The name of the declared function.
  public let identifier: Parsed<FunctionIdentifier>

  /// The compile-time parameters of the function.
  public let staticParameters: ContextParameters

  /// The capture-list of the function.
  public let captures: CaptureList

  /// The run-time parameters of the function.
  public let parameters: [ParameterDeclaration.ID]

  /// The effect of the function's call operator.
  public let effect: Parsed<AccessEffect>

  /// The type of the function's return value.
  public let output: ExpressionIdentity?

  /// The body of the function.
  public let body: [StatementIdentity]?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    annotations: [Annotation],
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Parsed<Introducer>,
    identifier: Parsed<FunctionIdentifier>,
    staticParameters: ContextParameters,
    captures: CaptureList,
    parameters: [ParameterDeclaration.ID],
    effect: Parsed<AccessEffect>,
    output: ExpressionIdentity?,
    body: [StatementIdentity]?,
    site: SourceSpan
  ) {
    self.annotations = annotations
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.staticParameters = staticParameters
    self.captures = captures
    self.parameters = parameters
    self.effect = effect
    self.output = output
    self.body = body
    self.site = site
  }

  /// `true` iff `self` declares a memberwise initializer.
  public var isMemberwiseInitializer: Bool {
    introducer.value == .memberwiseinit
  }

}

extension FunctionDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for a in annotations { result.append("\(printer.show(a))\n") }
    for m in modifiers { result.append("\(m) ") }

    switch introducer.value {
    case .fun: result.append("fun \(identifier.value)")
    case .`init`: result.append("init")
    case .memberwiseinit: result.append("memberwise init")
    }

    if !staticParameters.isEmpty {
      result.append(printer.show(staticParameters))
    }

    result.append(printer.show(captures))
    result.append("(")
    result.append(printer.show(parameters))
    result.append(")")

    if introducer.value == .fun {
      result.append(" \(effect.value) -> " + (output.map({ (o) in printer.show(o) }) ?? "Void"))
    }

    if let b = body {
      result.append(" {\n")
      for s in b { result.append(printer.show(s).indented + "\n") }
      result.append("}")
    }

    return result
  }

}

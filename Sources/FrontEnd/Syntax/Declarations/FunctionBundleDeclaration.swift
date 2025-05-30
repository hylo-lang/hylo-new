import Archivist
import Utilities

/// The declaration of a bundle of related functions.
@Archivable
public struct FunctionBundleDeclaration: RoutineDeclaration, Annotatable, Scope {

  /// The annotations on this declaration.
  public let annotations: [Annotation]

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Parsed<Token>

  /// The name of the declared function.
  public let identifier: Parsed<String>

  /// The compile-time parameters of the bundle.
  public let staticParameters: ContextParameters

  /// The capture-list of the function.
  public let captures: CaptureList

  /// The run-time parameters of the bundle.
  public let parameters: [ParameterDeclaration.ID]

  /// The effect of the bundle's call operator.
  public let effect: Parsed<AccessEffect>

  /// The type of the bundle's return value.
  public let output: ExpressionIdentity?

  /// The variants of the bundle.
  public let variants: [VariantDeclaration.ID]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    annotations: [Annotation],
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Parsed<Token>,
    identifier: Parsed<String>,
    staticParameters: ContextParameters,
    captures: CaptureList,
    parameters: [ParameterDeclaration.ID],
    effect: Parsed<AccessEffect>,
    output: ExpressionIdentity?,
    variants: [VariantDeclaration.ID],
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
    self.variants = variants
    self.site = site
  }

}

extension FunctionBundleDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }

    result.append("fun \(identifier.value)")

    if !staticParameters.isEmpty {
      result.append(printer.show(staticParameters))
    }

    result.append(printer.show(captures))
    result.append("(")
    result.append(printer.show(parameters))
    result.append(") \(effect.value) -> ")
    result.append(output.map({ (o) in printer.show(o) }) ?? "Void")

    result.append(" {\n")
    for v in variants {
      result.append(printer.show(v).indented + "\n")
    }
    result.append(output.map({ (o) in printer.show(o) }) ?? "}")

    return result
  }

}

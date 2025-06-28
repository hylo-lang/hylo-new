import Archivist
import Utilities

/// A generic parameter.
@Archivable
public enum GenericParameter: TypeTree {

  /// The generic parameter representing the conformer of a trait.
  case conformer(TraitDeclaration.ID, Kind)

  /// A generic parameter declared in sources.
  case user(GenericParameterDeclaration.ID, Kind)

  /// The `n`-th parameter of a built-in type.
  case nth(Int, Kind)

  /// The kind of this parameter.
  public var kind: Kind {
    switch self {
    case .conformer(_, let k), .user(_, let k), .nth(_, let k):
      return k
    }
  }

  /// The declaration of the parameter, unless it is predefined.
  public var declaration: GenericParameterDeclaration.ID? {
    if case .user(let d, _) = self { d } else { nil }
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension GenericParameter: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .conformer:
      return printer.uniquized("Self", for: self)
    case .user(let d, _):
      return printer.uniquized(printer.program[d].identifier.value, for: self)
    case .nth(let i, _):
      return printer.uniquized("T\(i)", for: self)
    }
  }

}

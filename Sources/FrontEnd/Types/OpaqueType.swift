import Archivist

/// A type whose definition is abtract in sources but known to the compiler.
@Archivable
public enum OpaqueType: TypeTree {

  /// An opaque type representing the inferred environment of a local abstraction.
  case environment(DeclarationIdentity)

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension OpaqueType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "some"
  }

}

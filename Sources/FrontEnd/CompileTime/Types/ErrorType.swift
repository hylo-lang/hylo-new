import Archivist

/// A type denoting a typing error.
@Archivable
public struct ErrorType: TypeTree {

  /// Creates an instance.
  public init() {}

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasError
  }

}

extension ErrorType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "#!"
  }

}

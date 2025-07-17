import Archivist

/// The unit type, aka `Hylo.Void`.
@Archivable
public struct VoidType: TypeTree {

  /// Creates an instance.
  public init() {}

  /// Properties about `self`.
  public var properties: TypeProperties {
    .init()
  }

}

extension VoidType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "Void"
  }

}

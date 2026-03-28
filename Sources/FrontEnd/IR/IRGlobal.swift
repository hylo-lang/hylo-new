/// A global constant in Hylo IR.
public struct IRGlobal: Hashable, Sendable {

  /// The type of the allocated storage.
  public let storageType: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// The function initializing the storage on the first access.
  public let initializer: IRFunction.Name

  /// Creates an instance with the given properties.
  public init(storageType: AnyTypeIdentity, alignment: IRAlignment, initializer: IRFunction.Name) {
    self.storageType = storageType
    self.alignment = alignment
    self.initializer = initializer
  }

}

extension IRGlobal: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "global of \(printer.show(storageType))"
  }

}

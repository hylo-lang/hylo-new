/// A global variable in Hylo IR.
public struct IRGlobal: Hashable, Sendable {

  /// The name of an global IR variable.
  public enum Name: Hashable, Sendable {

    /// The identity of a variable lowered from sources.
    case lowered(BindingDeclaration.ID)

  }

  /// The name of the variable.
  public let name: Name

  /// The type of the allocated storage.
  public let storageType: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// The function initializing the storage on the first access.
  public let initializer: IRFunction.ID

  /// Creates an instance with the given properties.
  public init(
    name: Name, storageType: AnyTypeIdentity, alignment: IRAlignment,
    initializer: IRFunction.ID
  ) {
    self.name = name
    self.storageType = storageType
    self.alignment = alignment
    self.initializer = initializer
  }

}

extension IRGlobal: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "global \(printer.show(name)) as \(printer.show(storageType)), \(printer.show(alignment))"
  }

}

extension IRGlobal.Name: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .lowered(let d):
      return printer.program.debugName(of: .init(d))
    }
  }

}

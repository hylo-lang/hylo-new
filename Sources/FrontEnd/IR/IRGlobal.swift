/// A global variable in Hylo IR.
public struct IRGlobal: Hashable, Sendable {

  /// The name of an global IR variable.
  public enum Name: Hashable, Sendable {

    /// The identity of a variable lowered from sources.
    case lowered(BindingDeclaration.ID)

    /// The identity of a type witness.
    ///
    /// This case is for naming global constants representing type witnesses. The payload is the
    /// type whose properties are witnessed. Note that this type is different from the type of the
    /// global constant itself.
    ///
    /// - Requires: The payload is dealiased.
    case witness(AnyTypeIdentity)

  }

  /// A function or constant defining the value initializing the storage.
  public enum Initializer: Hashable, Sendable {

    /// A function that called once, on the first access to the global.
    case function(IRFunction.ID)

    /// A constant type witness.
    case typeWitness(AnyTypeIdentity)

    /// The payload of `self` iff it is `.function`.
    public var function: IRFunction.ID? {
      if case .function(let f) = self {
        return f
      } else {
        return nil
      }
    }

  }

  /// The name of the variable.
  public let name: Name

  /// The type of the allocated storage.
  public let storageType: AnyTypeIdentity

  /// The alignment of the allocated storage.
  public let alignment: IRAlignment

  /// The function or constant defining the value initializing the storage.
  public let initializer: Initializer

  /// Creates an instance with the given properties.
  public init(
    name: Name, storageType: AnyTypeIdentity, alignment: IRAlignment, initializer: Initializer
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
    case .witness(let t):
      return "#witness(\(printer.show(t)))"
    }
  }

}

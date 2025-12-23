import Utilities

/// An object in an abstract interpreter.
internal struct AbstractObject<Domain: AbstractDomain>: Hashable, Sendable {

  /// The type of the object.
  internal let type: AnyTypeIdentity

  /// The value of the object.
  internal var value: Value

  /// Creates an instance with the given properties.
  internal init(type: AnyTypeIdentity, value: Value) {
    self.type = type
    self.value = value.canonical
  }

  /// Returns the result of calling `action` with the sub-object at given `offset`, using `typer`
  /// to compute abstract layouts.
  internal mutating func withSubobject<T>(
    _ offset: Int, computingLayoutWith typer: inout Typer,
    _ action: (inout AbstractObject, inout Typer) -> T
  ) -> T {
    let layout = typer.storage(of: type) ?? []
    var parts: [Value]

    if case .mixed(let ps) = value {
      parts = ps
    } else {
      parts = Array(repeating: value, count: layout.count)
    }

    var subobject = AbstractObject(type: layout[offset], value: parts[offset])
    defer {
      parts[offset] = subobject.value
      value = .mixed(parts).canonical
    }

    return action(&subobject, &typer)
  }

  /// Returns the result of calling `action` with the sub-object at given `path`, using `typer`
  /// to compute abstract layouts.
  internal mutating func withSubobject<T, Path: Collection<Int>>(
    at path: Path, computingLayoutWith typer: inout Typer,
    _ action: (inout AbstractObject, inout Typer) -> T
  ) -> T {
    if let (i, t) = path.headAndTail {
      return withSubobject(i, computingLayoutWith: &typer) { (o, tp) in
        o.withSubobject(at: t, computingLayoutWith: &tp, action)
      }
    } else {
      defer { value = value.canonical }
      return action(&self, &typer)
    }
  }

  /// Returns `l` merged with `r`.
  internal static func && (l: Self, r: Self) -> Self {
    precondition(l.type == r.type)
    return AbstractObject(type: l.type, value: l.value && r.value)
  }

}

extension AbstractObject {

  /// The value of an abstract object.
  internal enum Value: Hashable, Sendable {

    /// An object whose parts all have the same abstract value.
    case uniform(Domain)

    /// An object whose parts may have different values.
    ///
    /// - Requires: The payload is not empty.
    case mixed([Value])

    /// The canonical form of `self`.
    internal var canonical: Value {
      // Nothing do do if the object is already canonical.
      guard case .mixed(var parts) = self else { return self }

      // Compute the canonical form of each part and check if there are uniform.
      parts[0] = parts[0].canonical
      var partsAreUniform = parts[0].isUniform
      for i in 1 ..< parts.count {
        parts[i] = parts[i].canonical
        partsAreUniform = partsAreUniform && parts[i] == parts[0]
      }
      return partsAreUniform ? parts[0] : .mixed(parts)
    }

    /// `true` if `self` is notionally uniform.
    private var isUniform: Bool {
      if case .uniform = self { return true } else { return false }
    }

    /// Returns `lhs` merged with `rhs`.
    internal static func && (lhs: Self, rhs: Self) -> Self {
      switch (lhs.canonical, rhs.canonical) {
      case (.uniform(let lhs), .uniform(let rhs)):
        return .uniform(lhs && rhs)
      case (.mixed(let lhs), .mixed(let rhs)):
        return .mixed(zip(lhs, rhs).map(&&))
      case (.mixed(let lhs), _):
        return .mixed(lhs.map({ $0 && rhs }))
      case (_, .mixed(let rhs)):
        return .mixed(rhs.map({ lhs && $0 }))
      }
    }

  }

}

extension AbstractObject: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(value)) as \(printer.show(type))"
  }

}

extension AbstractObject.Value: Showable {

  /// Returns a textual representation of `self` using `printer`.
  internal func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .uniform(let s):
      return printer.show(s)
    case .mixed(let s):
      return "{\(printer.show(s))}"
    }
  }

}

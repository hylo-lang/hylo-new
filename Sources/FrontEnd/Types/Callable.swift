/// A witness that some simple (i.e., without context) type denotes an abstraction.
public struct Callable {

  /// The way in which the abstraction must be applied.
  public let style: Call.Style

  /// The environment of the abstraction.
  public let environment: AnyTypeIdentity

  /// The input labels and types of the abstraction.
  public let inputs: [Parameter]

  /// The type of the abstraction's result.
  public let output: AnyTypeIdentity

  /// Creates an instance from an arrow type.
  public init(_ a: Arrow) {
    self.style = .parenthesized
    self.environment = a.environment
    self.inputs = a.inputs
    self.output = a.output
  }

  /// The labels associated with each input.
  public var labels: some Sequence<String?> {
    inputs.lazy.map(\.label)
  }

  /// Returns `true` iff instances of the witnessee can be applied with `style` and `labels`.
  public func labelsCompatible<T: Collection<String?>>(with labels: T) -> Bool {
    var i = labels.startIndex
    for p in inputs {
      // Is there's an explicit argument with the right label?
      if (labels.endIndex > i) && (labels[i] == p.label) {
        labels.formIndex(after: &i)
      }

      // The parameter has a default value?
      else if p.defaultValue != nil {
        continue
      }

      // Arguments do not match.
      else {
        return false
      }
    }

    return i == labels.endIndex
  }

}

extension Callable: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let e = printer.show(environment)
    let i = printer.show(inputs)
    let o = printer.show(output)
    switch style {
    case .parenthesized:
      return "[\(e)](\(i)) -> \(o)"
    case .bracketed:
      return "[\(e)](\(i)) [-]> \(o)"
    }
  }

}

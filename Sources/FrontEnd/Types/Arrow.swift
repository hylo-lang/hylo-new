import Archivist
import Utilities

/// The type of term abstraction.
@Archivable
public struct Arrow: TypeTree {

  /// The way in which the abstraction must be applied.
  public let style: Call.Style

  /// The effect of the abstraction's call operator.
  public let effect: AccessEffect

  /// The environment of the abstraction.
  public let environment: AnyTypeIdentity

  /// The input labels and types of the abstraction.
  public let inputs: [Parameter]

  /// The output type of the abstraction.
  public let output: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(
    style: Call.Style = .parenthesized,
    effect: AccessEffect = .let,
    environment: AnyTypeIdentity = .void,
    inputs: [Parameter],
    output: AnyTypeIdentity
  ) {
    self.style = style
    self.effect = effect
    self.environment = environment
    self.inputs = inputs
    self.output = output
  }

  /// Creates an instance from `inputs`, which denote unlabeled `let` parameters, to `output`,
  /// having no environment and the `let` effect.
  public init<T: TypeIdentity>(_ inputs: MachineType.ID..., to output: T) {
    self.init(
      inputs: inputs.map({ (i) in .init(access: .let, type: i.erased) }),
      output: output.erased)
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    inputs.reduce(output.properties, { (a, i) in a.union(i.type.properties) })
  }

  /// The labels associated with each input.
  public var labels: some Sequence<String?> {
    inputs.lazy.map(\.label)
  }

  /// Returns `true` iff instances of `self` can be applied with `labels`.
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

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Arrow {
    .init(
      effect: effect,
      environment: store.map(environment, transform),
      inputs: inputs.map({ (p) in p.modified(in: &store, by: transform) }),
      output: store.map(output, transform))
  }

}

extension Arrow: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let e = printer.show(environment)
    let i = printer.show(inputs)
    let o = printer.show(output)
    return "[\(e)](\(i)) \(effect) -> \(o)"
  }

}

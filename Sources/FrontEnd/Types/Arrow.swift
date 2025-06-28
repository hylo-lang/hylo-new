import Archivist
import Utilities

/// The type of term abstraction returning independent values.
@Archivable
public struct Arrow: TypeTree {

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
    effect: AccessEffect = .let,
    environment: AnyTypeIdentity = .void,
    inputs: [Parameter],
    output: AnyTypeIdentity
  ) {
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

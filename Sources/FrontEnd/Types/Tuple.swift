import Archivist
import Utilities

/// The type of a tuple.
@Archivable
public struct Tuple: TypeTree {

  /// An element in a tuple type.
  @Archivable
  public struct Element: Hashable, Sendable {

    /// The label of the element.
    public let label: String?

    /// The type of the element.
    public let type: AnyTypeIdentity

    /// Creates an instance with the given properties.
    public init(label: String?, type: AnyTypeIdentity) {
      self.label = label
      self.type = type
    }

    /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
    public func modified(
      in store: inout TypeStore,
      by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
    ) -> Element {
      .init(label: label, type: store.map(type, transform))
    }

  }

  /// The elements of the tuple.
  public let elements: [Element]

  /// Creates an instance with the given properties.
  public init<S: Sequence<Element>>(elements: S) {
    self.elements = Array(elements)
  }

  /// Creates an instance with the given types, without any labels.
  public init<T: Sequence<AnyTypeIdentity>>(types: T) {
    self.init(elements: types.map({ (t) in .init(label: nil, type: t) }))
  }

  /// Properties about `self`.
  public var properties: TypeProperties {
    elements.reduce([], { (a, e) in a.union(e.type.properties) })
  }

  /// The labels associated with each element.
  public var labels: some Sequence<String?> {
    elements.lazy.map(\.label)
  }

  /// Returns `true` iff the labels of the elements in `self` are equal to the labels of the
  /// elements in `other`, which are at `path`.
  public func labelsEqual<T: Sequence>(_ other: T, _ path: KeyPath<T.Element, String?>) -> Bool {
    elements.elementsEqual(other, by: { (a, b) in a.label == b[keyPath: path] })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Tuple {
    .init(elements: elements.map({ (e) in e.modified(in: &store, by: transform) }))
  }

}

extension Tuple: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let (h, t) = elements.headAndTail {
      if (h.label == nil) && t.allSatisfy({ (e) in (e.type == h.type) && (e.label == nil) }) {
        return "\(printer.show(h.type))[\(elements.count)]"
      } else {
        return "{\(printer.show(elements))}"
      }
    } else {
      return "Void"
    }
  }

}

extension Tuple.Element: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let t = printer.show(type)
    return if let l = label { "\(l): \(t)" } else { t }
  }

}

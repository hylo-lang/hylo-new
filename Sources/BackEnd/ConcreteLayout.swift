import SwiftyLLVM

/// A description of the layout of a Hylo for a particular host.
internal struct ConcreteLayout {

  /// The LLVM types of the fields constituting the parts of an instance, if any.
  ///
  /// This property may be empty if the type described by `self` has no stored property, either
  /// because it is opaque or because it is a machine type.
  internal let fields: [SwiftyLLVM.AnyType.UnsafeReference]

  /// A map from the index of a property to the index of its corresponding field, or `-1` if that
  /// property's representation is erased.
  ///
  /// - Invariant: the lenght of `propertyToField` is greater than or equal to that of `fields`.
  internal let propertyToField: [Int]

  /// The size of an instance, in bytes.
  internal let size: Int

  /// The alignment requirement.
  internal let alignment: Int

}

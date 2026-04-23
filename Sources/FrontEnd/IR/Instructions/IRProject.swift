import Utilities

/// Projects a value by invoking the ramp of a subscript.
public struct IRProject: IRRegionEntry {

  /// The operands of the instruction.
  public let operands: [IRValue]

  /// The region of the code corresponding to this instruction.
  public let anchor: Anchor

  /// The type of the projected value.
  public let projectee: AnyTypeIdentity

  /// The capabilities of the projection.
  public let access: AccessEffect

  /// Creates an instance with the given properties.
  public init(
    callee: IRValue, arguments: [IRValue], projectee: AnyTypeIdentity, access: AccessEffect,
    anchor: Anchor
  ) {
    var operands = Array<IRValue>(minimumCapacity: arguments.count + 1)
    operands.append(callee)
    operands.append(contentsOf: arguments)

    self.operands = operands
    self.anchor = anchor
    self.projectee = projectee
    self.access = access
  }

  /// Creates a copy of `other`, substituting its properties with `ss`.
  public init(_ other: Self, substituting ss: IRSubstitutionTable) {
    self.operands = other.operands.map({ (o) in ss[o] })
    self.anchor = other.anchor
    self.projectee = other.projectee
    self.access = other.access
  }

  /// The subscript being applied.
  public var callee: IRValue {
    operands[0]
  }

  /// The arguments of the call.
  public var arguments: ArraySlice<IRValue> {
    operands[1...]
  }

  /// The type of the instruction's result.
  public var type: IRType {
    .place(projectee)
  }

  /// `true`.
  public var isExtendingOperandLifetimes: Bool {
    true
  }

  /// Asserts that the well-formedness conditions of the instruction hold.
  ///
  /// Returns `true` iff the following conditions hold:
  ///
  /// * The callee is a term abstraction.
  /// * The callee is a constant and the call effect of its type is `.let` or the callee is an
  ///   access that supports the call effect of its type.
  /// * Each argument supports the effect of its corresponding parameter.
  public func assertWellFormed(in parent: IRFunction, using program: inout Program) -> Bool {
    // The callee is a term abstraction.
    guard
      let t = parent.result(of: callee),
      let f = program.types.seenAsTermAbstraction(t.type),
      t.isPlace
    else { preconditionFailure() }

    // The callee supports the effect of the projection being applied.
    switch program.types[f].effect {
    case .let:
      precondition(callee.isConstant || parent.isAccess(callee, .let))
    case let k:
      precondition(parent.isAccess(callee, k))
    }

    // Each argument supports the effect of its corresponding parameter.
    precondition(program.types[f].inputs.count == arguments.count)
    for (p, v) in zip(program.types[f].inputs, arguments) {
      precondition(parent.isAccess(v, p.access))
    }

    return true
  }

}

extension IRProject: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "project \(printer.show(callee))[\(printer.show(arguments))]"
  }

}

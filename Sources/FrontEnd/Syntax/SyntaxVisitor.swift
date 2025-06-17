import Utilities

/// A collection of callbacks for visiting an abstract syntax tree.
///
/// Use this protocol to implement algorithms that traverse all or most nodes of an abstract syntax
/// tree and perform similar operations on each of them. Instances of conforming types are meant to
/// be passed as argument to `Syntax.visit(_:calling:)`.
public protocol SyntaxVisitor {

  /// Called when the node `node`, which is in `program`, is about to be entered; returns `false`
  /// if traversal should skip `node`.
  ///
  /// Use this method to perform actions before a node is being traversed and/or customize how the
  /// tree is traversed. If the method returns `true`, `willEnter` will be called before visiting
  /// each child of `node` and `willExit` will be called when `node` is left. If the method returns
  /// `false`, neither `willEnter` nor `willExit` will be called for `node` and its children.
  mutating func willEnter(_ node: AnySyntaxIdentity, in program: Program) -> Bool

  /// Called when the node `node`, which is in `program`, is about to be left.
  mutating func willExit(_ node: AnySyntaxIdentity, in program: Program)

}

extension SyntaxVisitor {

  public mutating func willEnter(_ node: AnySyntaxIdentity, in program: Program) -> Bool { true }

  public mutating func willExit(_ node: AnySyntaxIdentity, in program: Program) {}

}

extension Program {

  /// Calls `visit(_:calling:)` on the abstract syntax tree of `m`.
  public func visit<T: SyntaxVisitor>(_ m: ModuleIdentity, calling v: inout T) {
    for (i, s) in self[m].sources.values.enumerated() {
      for o in s.syntax.indices {
        let f = Program.SourceFileIdentity(module: m, offset: i)
        visit(AnySyntaxIdentity(file: f, offset: o), calling: &v)
      }
    }
  }

  /// Visits `n` and its children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor>(_ n: AnySyntaxIdentity, calling v: inout T) {
    if !v.willEnter(n, in: self) { return }
    switch tag(of: n) {
    case AssociatedTypeDeclaration.self:
      break
    case BindingDeclaration.self:
      traverse(castUnchecked(n, to: BindingDeclaration.self), calling: &v)
    case ConformanceDeclaration.self:
      traverse(castUnchecked(n, to: ConformanceDeclaration.self), calling: &v)
    case EnumCaseDeclaration.self:
      traverse(castUnchecked(n, to: EnumCaseDeclaration.self), calling: &v)
    case EnumDeclaration.self:
      traverse(castUnchecked(n, to: EnumDeclaration.self), calling: &v)
    case ExtensionDeclaration.self:
      traverse(castUnchecked(n, to: ExtensionDeclaration.self), calling: &v)
    case FunctionBundleDeclaration.self:
      traverse(castUnchecked(n, to: FunctionBundleDeclaration.self), calling: &v)
    case FunctionDeclaration.self:
      traverse(castUnchecked(n, to: FunctionDeclaration.self), calling: &v)
    case GenericParameterDeclaration.self:
      traverse(castUnchecked(n, to: GenericParameterDeclaration.self), calling: &v)
    case ImportDeclaration.self:
      break
    case ParameterDeclaration.self:
      traverse(castUnchecked(n, to: ParameterDeclaration.self), calling: &v)
    case StructDeclaration.self:
      traverse(castUnchecked(n, to: StructDeclaration.self), calling: &v)
    case TraitDeclaration.self:
      traverse(castUnchecked(n, to: TraitDeclaration.self), calling: &v)
    case TypeAliasDeclaration.self:
      traverse(castUnchecked(n, to: TypeAliasDeclaration.self), calling: &v)
    case UsingDeclaration.self:
      traverse(castUnchecked(n, to: UsingDeclaration.self), calling: &v)
    case VariableDeclaration.self:
      break
    case VariantDeclaration.self:
      traverse(castUnchecked(n, to: VariantDeclaration.self), calling: &v)
    case UsingDeclaration.self:
      traverse(castUnchecked(n, to: UsingDeclaration.self), calling: &v)

    case ArrowExpression.self:
      traverse(castUnchecked(n, to: ArrowExpression.self), calling: &v)
    case BooleanLiteral.self:
      break
    case Call.self:
      traverse(castUnchecked(n, to: Call.self), calling: &v)
    case Conversion.self:
      traverse(castUnchecked(n, to: Conversion.self), calling: &v)
    case EqualityWitnessExpression.self:
      traverse(castUnchecked(n, to: EqualityWitnessExpression.self), calling: &v)
    case If.self:
      traverse(castUnchecked(n, to: If.self), calling: &v)
    case ImplicitQualification.self:
      break
    case InoutExpression.self:
      traverse(castUnchecked(n, to: InoutExpression.self), calling: &v)
    case IntegerLiteral.self:
      break
    case KindExpression.self:
      traverse(castUnchecked(n, to: KindExpression.self), calling: &v)
    case Lambda.self:
      traverse(castUnchecked(n, to: Lambda.self), calling: &v)
    case NameExpression.self:
      traverse(castUnchecked(n, to: NameExpression.self), calling: &v)
    case New.self:
      traverse(castUnchecked(n, to: New.self), calling: &v)
    case PatternMatch.self:
      traverse(castUnchecked(n, to: PatternMatch.self), calling: &v)
    case PatternMatchCase.self:
      traverse(castUnchecked(n, to: PatternMatchCase.self), calling: &v)
    case RemoteTypeExpression.self:
      traverse(castUnchecked(n, to: RemoteTypeExpression.self), calling: &v)
    case StaticCall.self:
      traverse(castUnchecked(n, to: StaticCall.self), calling: &v)
    case StringLiteral.self:
      break
    case SumTypeExpression.self:
      traverse(castUnchecked(n, to: SumTypeExpression.self), calling: &v)
    case SynthethicExpression.self:
      break
    case TupleLiteral.self:
      traverse(castUnchecked(n, to: TupleLiteral.self), calling: &v)
    case TupleTypeExpression.self:
      traverse(castUnchecked(n, to: TupleTypeExpression.self), calling: &v)
    case WildcardLiteral.self:
      break

    case BindingPattern.self:
      traverse(castUnchecked(n, to: BindingPattern.self), calling: &v)
    case ExtractorPattern.self:
      traverse(castUnchecked(n, to: ExtractorPattern.self), calling: &v)
    case TuplePattern.self:
      traverse(castUnchecked(n, to: TuplePattern.self), calling: &v)

    case Assignment.self:
      traverse(castUnchecked(n, to: Assignment.self), calling: &v)
    case Block.self:
      traverse(castUnchecked(n, to: Block.self), calling: &v)
    case Discard.self:
      traverse(castUnchecked(n, to: Discard.self), calling: &v)
    case Return.self:
      traverse(castUnchecked(n, to: Return.self), calling: &v)

    default:
      unexpected(n)
    }
    v.willExit(n, in: self)
  }

  /// Visits `n` and its children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor, U: SyntaxIdentity>(_ n: U?, calling v: inout T) {
    n.map({ (m) in visit(m.erased, calling: &v) })
  }

  /// Visits `ns` and their children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor, U: Collection>(
    _ ns: U, calling v: inout T
  ) where U.Element: SyntaxIdentity {
    for n in ns {
      visit(n.erased, calling: &v)
    }
  }

  /// Visits `ps` and their children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor>(_ ps: ContextParameters, calling v: inout T) {
    visit(ps.explicit, calling: &v)
    visit(ps.implicit, calling: &v)
  }

  /// Visits `cs` and their children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor>(_ cs: CaptureList, calling v: inout T) {
    visit(cs.explicit, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: BindingDeclaration.ID, calling v: inout T) {
    visit(self[n].pattern, calling: &v)
    visit(self[n].initializer, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ConformanceDeclaration.ID, calling v: inout T) {
    visit(self[n].staticParameters, calling: &v)
    visit(self[n].witness, calling: &v)
    if let b = self[n].members { visit(b, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: EnumCaseDeclaration.ID, calling v: inout T) {
    visit(self[n].parameters, calling: &v)
    visit(self[n].body, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: EnumDeclaration.ID, calling v: inout T) {
    visit(self[n].staticParameters, calling: &v)
    visit(self[n].representation, calling: &v)
    visit(self[n].conformances, calling: &v)
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ExtensionDeclaration.ID, calling v: inout T) {
    visit(self[n].staticParameters, calling: &v)
    visit(self[n].extendee, calling: &v)
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: FunctionBundleDeclaration.ID, calling v: inout T) {
    visit(self[n].staticParameters, calling: &v)
    visit(self[n].captures, calling: &v)
    visit(self[n].parameters, calling: &v)
    visit(self[n].output, calling: &v)
    visit(self[n].variants, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: FunctionDeclaration.ID, calling v: inout T) {
    visit(self[n].staticParameters, calling: &v)
    visit(self[n].captures, calling: &v)
    visit(self[n].parameters, calling: &v)
    visit(self[n].output, calling: &v)
    if let b = self[n].body { visit(b, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: GenericParameterDeclaration.ID, calling v: inout T) {
    visit(self[n].ascription, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ParameterDeclaration.ID, calling v: inout T) {
    visit(self[n].ascription, calling: &v)
    visit(self[n].defaultValue, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: StructDeclaration.ID, calling v: inout T) {
    visit(self[n].staticParameters, calling: &v)
    visit(self[n].conformances, calling: &v)
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TraitDeclaration.ID, calling v: inout T) {
    visit(self[n].parameters, calling: &v)
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TypeAliasDeclaration.ID, calling v: inout T) {
    visit(self[n].aliasee, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: UsingDeclaration.ID, calling v: inout T) {
    visit(self[n].witness, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: VariantDeclaration.ID, calling v: inout T) {
    if let b = self[n].body { visit(b, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ArrowExpression.ID, calling v: inout T) {
    visit(self[n].environment, calling: &v)
    for p in self[n].parameters { visit(p.ascription, calling: &v) }
    visit(self[n].output, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Call.ID, calling v: inout T) {
    visit(self[n].callee, calling: &v)
    for a in self[n].arguments { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: EqualityWitnessExpression.ID, calling v: inout T) {
    visit(self[n].lhs, calling: &v)
    visit(self[n].rhs, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: If.ID, calling v: inout T) {
    visit(self[n].conditions, calling: &v)
    visit(self[n].success, calling: &v)
    visit(self[n].failure, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: InoutExpression.ID, calling v: inout T) {
    visit(self[n].lvalue, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: KindExpression.ID, calling v: inout T) {
    if case .arrow(let a, let b) = self[n].value {
      visit(a, calling: &v)
      visit(b, calling: &v)
    }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Lambda.ID, calling v: inout T) {
    visit(self[n].function, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: NameExpression.ID, calling v: inout T) {
    visit(self[n].qualification, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: New.ID, calling v: inout T) {
    visit(self[n].qualification, calling: &v)
    visit(self[n].target, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Conversion.ID, calling v: inout T) {
    visit(self[n].source, calling: &v)
    visit(self[n].target, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: PatternMatch.ID, calling v: inout T) {
    visit(self[n].scrutinee, calling: &v)
    visit(self[n].branches, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: PatternMatchCase.ID, calling v: inout T) {
    visit(self[n].pattern, calling: &v)
    visit(self[n].body, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: RemoteTypeExpression.ID, calling v: inout T) {
    visit(self[n].projectee, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: StaticCall.ID, calling v: inout T) {
    visit(self[n].callee, calling: &v)
    visit(self[n].arguments, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: SumTypeExpression.ID, calling v: inout T) {
    visit(self[n].elements, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TupleLiteral.ID, calling v: inout T) {
    for a in self[n].elements { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TupleTypeExpression.ID, calling v: inout T) {
    for a in self[n].elements { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: BindingPattern.ID, calling v: inout T) {
    visit(self[n].pattern, calling: &v)
    visit(self[n].ascription, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ExtractorPattern.ID, calling v: inout T) {
    visit(self[n].extractor, calling: &v)
    for a in self[n].elements { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TuplePattern.ID, calling v: inout T) {
    for a in self[n].elements { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Assignment.ID, calling v: inout T) {
    visit(self[n].lhs, calling: &v)
    visit(self[n].rhs, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Block.ID, calling v: inout T) {
    visit(self[n].statements, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Discard.ID, calling v: inout T) {
    visit(self[n].value, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Return.ID, calling v: inout T) {
    visit(self[n].value, calling: &v)
  }

}

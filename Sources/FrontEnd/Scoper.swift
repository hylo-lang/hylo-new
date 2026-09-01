import Utilities

/// A function computing the scoping relationships of a module.
public struct Scoper {

  /// Creates an instance.
  public init() {}

  /// Computes the scoping relationships in `m`, which is in `p`.
  public func visit(_ m: Module.ID, of p: inout Program) async {
    let ts = p[m].sources.values.indices.map { (i) in
      Task.detached { [p] in Self.scope(sourceAt: i, of: m, in: p) }
    }

    for (i, t) in ts.enumerated() {
      install(await t.value, asScopesOfSourceAt: i, of: m, in: &p)
    }
  }

  /// Computes the scoping relationships in `m`, which is in `p`, on the calling thread.
  ///
  /// Unlike `visit(_:of:)`, this method scopes one source after another rather than one per
  /// task. It is meant for hosts that cannot run Swift's cooperative executor, such as a
  /// WebAssembly guest driven through exported functions rather than through an entry point.
  public func visitSerially(_ m: Module.ID, of p: inout Program) {
    for i in p[m].sources.values.indices {
      install(Self.scope(sourceAt: i, of: m, in: p), asScopesOfSourceAt: i, of: m, in: &p)
    }
  }

  /// Returns the scoping relationships in the `i`-th source of `m`, which is in `p`.
  private static func scope(sourceAt i: Int, of m: Module.ID, in p: Program) -> Visitor {
    let f = SourceFile.ID(module: m, offset: i)
    var v = Visitor(p[f])
    for n in p[f].roots {
      p.visit(n, calling: &v)
    }
    return v
  }

  /// Writes the relationships that `v` computed into the `i`-th source of `m`, which is in `p`.
  private func install(
    _ v: consuming Visitor, asScopesOfSourceAt i: Int, of m: Module.ID, in p: inout Program
  ) {
    let f = SourceFile.ID(module: m, offset: i)
    modify(&p[f]) { (w) in
      swap(&w.topLevelDeclarations, &v.topLevelDeclarations)
      swap(&w.syntaxToParent, &v.syntaxToParent)
      swap(&w.scopeToDeclarations, &v.scopeToDeclarations)
      swap(&w.variableToBinding, &v.variableToBinding)
    }
    assert(p[f].syntax.count == v.syntaxToParent.count)
  }

  /// The computation of the scoping relationships in a single source file.
  private struct Visitor: SyntaxVisitor, Sendable {

    /// The top-level declarations in the file.
    var topLevelDeclarations: [DeclarationIdentity]

    /// A table from syntax tree to the scope that contains it.
    var syntaxToParent: [Int]

    /// A table from scope to the declarations that it contains directly.
    var scopeToDeclarations: [Int: [DeclarationIdentity]]

    /// A table from variable declaration to its containing binding declaration, if any.
    var variableToBinding: [Int: BindingDeclaration.ID]

    /// The innermost lexical scope currently visited.
    var innermostScope: Int

    /// The binding declarations currently visited, from outermost to innermost.
    var bindingDeclarationsOnStack: [BindingDeclaration.ID]

    /// Creates an instance for computing the relationships of `f`.
    init(_ f: Module.SourceContainer) {
      self.topLevelDeclarations = []
      self.syntaxToParent = f.syntaxToParent
      self.scopeToDeclarations = [:]
      self.variableToBinding = [:]
      self.innermostScope = -1
      self.bindingDeclarationsOnStack = []
    }

    mutating func willEnter(_ n: AnySyntaxIdentity, in program: Program) -> Bool {
      syntaxToParent[n.offset] = innermostScope

      // Conditional expression require special handling.
      if let e = program.cast(n, to: If.self) {
        // The conditions and success branch are in the scope of the expression.
        innermostScope = n.offset
        scopeToDeclarations[innermostScope] = []
        program.visit(program[e].conditions, calling: &self)
        program.visit(program[e].success, calling: &self)

        // The failure branch is in the scope of the expression's parent.
        innermostScope = syntaxToParent[e.offset]
        program.visit(program[e].failure, calling: &self)
        return false
      }

      switch program.tag(of: n) {
      case BindingDeclaration.self:
        bindingDeclarationsOnStack.append(.init(uncheckedFrom: n))
      case VariableDeclaration.self:
        variableToBinding[n.offset] = bindingDeclarationsOnStack.last
      default:
        break
      }

      if let m = program.castToDeclaration(n) {
        if innermostScope >= 0 {
          scopeToDeclarations[innermostScope]!.append(m)
        } else {
          topLevelDeclarations.append(m)
        }
      }

      if program.isScope(n) {
        innermostScope = n.offset
        scopeToDeclarations[innermostScope] = []
      }

      return true
    }

    mutating func willExit(_ n: AnySyntaxIdentity, in program: Program) {
      if program.tag(of: n) == BindingDeclaration.self {
        bindingDeclarationsOnStack.removeLast()
      } else if program.isScope(n) {
        innermostScope = syntaxToParent[n.offset]
      }
    }

  }

}

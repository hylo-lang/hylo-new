import FrontEnd
import StandardLibrary

extension Program {

  /// A test program.
  static var test: Program {
    var p = Program(forTesting: true)

    let m0 = p.demandModule(.init("M0"))
    _ = p[m0].addSource(
      """
      trait P { type X }
      """)
    _ = p[m0].addSource(
      """
      trait Q { type Y }
      """)

    let m1 = p.demandModule(.init("M1"))
    p[m1].addDependency(p[m0].name)
    _ = p[m1].addSource(
      """
      trait R { type Z }
      """)

    let m2 = p.demandModule(.init("M2"))
    p[m2].addDependency(p[m0].name)
    _ = p[m2].addSource(
      """
      trait R { type Z }
      """)

    return p
  }

  /// Creates an instance with a minimal standard library, ready for testing.
  static func withMinimalStandardLibrary() async -> Program {
    var p = Program(forTesting: true)
    let m = p.demandModule(Module.standardLibraryName)
    _ = p[m].addSource(
      """
      @_symbol("Bool")
      public struct Bool { public memberwise init  }

      @_symbol("Int")
      public struct Int { public memberwise init }

      @_symbol("Int64")
      public struct Int64 { public memberwise init }
      """)
    return await p.typeChecked()
  }

  /// Creates an instance with the standard library loaded and type checked.
  static func withStandardLibrary() async throws -> Program {
    var p = Program(forTesting: true)
    let m = p.demandModule(Module.standardLibraryName)
    try SourceFile.forEach(in: StandardLibrary.localStandardLibrarySources) { (s) in
      p[m].addSource(s)
    }
    return await p.typeChecked()
  }

  /// Adds and returns the identity of a new module named `name`, having a single source file with
  /// the contents of `source`, and depending on the standard library.
  mutating func addUserModule(named name: String, source: SourceFile) -> Module.ID {
    let m = demandModule(Module.Name(name))
    _ = self[m].addSource(source)
    self[m].addDependency(Module.standardLibraryName)
    return m
  }

  /// Returns `self` with the scoping relationships computed in all modules.
  func scoped() async -> Self {
    var q = self
    for m in moduleIdentities {
      await q.assignScopes(m)
    }
    return q
  }

  /// Returns `self` with all modules type checked.
  func typeChecked() async -> Self {
    var q = await self.scoped()
    for m in moduleIdentities {
      q.assignTypes(m, loggingInferenceWhere: nil)
    }
    return q
  }

}

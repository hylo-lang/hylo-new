import FrontEnd

extension Program {

  /// A test program.
  static var test: Program {
    var p = Program()

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

  /// An instance with a minimal standard library, ready for testing.
  static func testProgramWithMinimalStandardLibrary() async -> Program {
    var r = Program(allowPartialStandardLibrary: true)
    let standardLibraryModule = r.demandModule(Module.standardLibraryName)
    _ = r[standardLibraryModule].addSource(
      """
      @_symbol("Bool")
      public struct Bool {
        public memberwise init
      }
      @_symbol("Int")
      public struct Int {
        public memberwise init
      }
      @_symbol("Int64")
      public struct Int64 {
        public memberwise init
      }
      """)
    return await r.typeChecked()
  }

  /// Adds a new module named `name` with source `source`, making it depend on the
  /// standard library, and returns its identity.
  mutating func addModule(named name: String, source: SourceFile) -> Module.ID {
    let m = demandModule(Module.Name(name))
    _ = self[m].addSource(source)
    self[m].addDependency(Module.standardLibraryName)
    return m
  }

  /// Returns `self` with the scoping relationships computed.
  func scoped() async -> Self {
    var q = self
    for m in moduleIdentities {
      await q.assignScopes(m)
    }
    return q
  }

  /// Returns `self` with the types checked.
  func typeChecked() async -> Self {
    var q = await self.scoped()
    for m in moduleIdentities {
      q.assignTypes(m, loggingInferenceWhere: nil)
    }
    return q
  }

}

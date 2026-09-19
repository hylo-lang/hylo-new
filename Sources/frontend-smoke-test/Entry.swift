import Foundation
import FrontEnd
import StandardLibrary

/// A minimal test runner verifying that the compiler's front-end works.
///
/// This is needed in the WASM target, where XCTest is not available.
@main
struct FrontEndSmokeTest {

  /// The root folder of the standard library's sources, which is given as the first command line
  /// argument because deriving it from `Bundle.module` traps on WASI.
  static var standardLibraryRoot: URL {
    guard let p = CommandLine.arguments.dropFirst().first else {
      fatalError("expected the root folder of the standard library's sources as an argument")
    }
    return URL(fileURLWithPath: p)
  }

  static func main() async throws {
    var p = Program(forTesting: true)

    let s = p.demandModule(Module.standardLibraryName)
    try SourceFile.forEach(in: standardLibraryRoot) { (f) in
      _ = p[s].addSource(f)
    }

    let m = p.demandModule(.init("Test"))
    p[m].addDependency(Module.standardLibraryName)
    _ = p[m].addSource(
      """
      fun use<T>(x: T) {}

      public fun main() {
        var x = 40
        &x = x + 2
        use(x == 42)
      }
      """)

    for m in p.moduleIdentities {
      await p.assignScopes(m)
    }
    for m in p.moduleIdentities {
      p.assignTypes(m, loggingInferenceWhere: nil)
    }
    for m in p.moduleIdentities {
      p.applyTransformationPasses(m)
    }

    let ds = Array(p.diagnostics)
    if !ds.isEmpty {
      print("FAILURE: \(ds.count) diagnostic(s) reported: \(ds.descriptions(joinedBy: "\n"))")
      exit(1)
    }
  }

}

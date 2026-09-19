import Foundation
import FrontEnd
import StandardLibrary

/// A minimal test runner verifying that the compiler's front-end works.
///
/// This is needed in the WASM target, where XCTest is not available.
@main
struct FrontEndSmokeTest {

  /// The root folder of the standard library's sources.
  ///
  /// `Bundle.module` reaches `Bundle.main`, whose initialization traps on WASI, so the root is
  /// taken from the command line when one is given and only falls back to the resource bundle on
  /// platforms where reading it is safe.
  static var standardLibraryRoot: URL {
    if let p = CommandLine.arguments.dropFirst().first {
      return URL(fileURLWithPath: p)
    } else {
      return bundledStandardLibrarySources
    }
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

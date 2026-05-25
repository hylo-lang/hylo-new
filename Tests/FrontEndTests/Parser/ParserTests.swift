import XCTest

@testable import FrontEnd

final class ParserTests: XCTestCase {

  /// Tests that the parser can parse a simple program without error.
  func testParse() throws {
    let input = """
      public fun main() {
        print("Hello, World!")
      }
      """
    let m = try testModule(contents: input)
    XCTAssertFalse(m.containsError, "Parsing failed with error: \(m.diagnostics)")
  }

  // MARK: Conditional compilation

  /// Tests that a simple conditional compilation statement is parsed correctly.
  func testSimpleConditionalCompilation() throws {
    let input = """
      #if os(macOs)
      foo()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    assert(c.condition, isOsOf: "macOs")
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)
  }

  /// Tests the parsing of a conditional compilation statement with a `true` condition.
  func testConditionalCompilationTrue() throws {
    let input = """
      #if true
      foo()
      #else
      awgr()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(c.condition, .`true`)
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 1)
  }

  /// Tests the parsing of a conditional compilation statement with a `false` condition.
  func testConditionalCompilationFalse() throws {
    let input = """
      #if false
      awgr()
      #else
      foo()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(c.condition, .`false`)
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 1)
  }

  /// Tests the parsing of a conditional compilation statement with an `os` condition.
  func testConditionalCompilationOs() throws {
    let input =
      """
      #if os(macOs)
      foo()
      #elseif os(Linux)
      bar()
      #elseif os(Windows)
      bazz()
      #else
      awgr()
      #endif
      """
    let (c, m) = try parseConditionalCompilation(input)
    assert(c.condition, isOsOf: "macOs")
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 1)

    let c2 = try XCTUnwrap(m[c.fallback[0]] as? ConditionalCompilation)
    assert(c2.condition, isOsOf: "Linux")
    XCTAssertEqual(c2.statements.count, 1)
    XCTAssertEqual(c2.fallback.count, 1)

    let c3 = try XCTUnwrap(m[c2.fallback[0]] as? ConditionalCompilation)
    assert(c3.condition, isOsOf: "Windows")
    XCTAssertEqual(c3.statements.count, 1)
    XCTAssertEqual(c3.fallback.count, 1)
  }

  /// Tests the parsing of a conditional compilation statement with an `arch` condition.
  func testConditionalCompilationArch() throws {
    let input =
      """
      #if arch(x86_64)
      foo()
      #elseif arch(i386)
      bar()
      #elseif arch(arm64)
      bazz()
      #elseif arch(arm)
      fizz()
      #else
      awgr()
      #endif
      """
    let (c, m) = try parseConditionalCompilation(input)
    assert(c.condition, isArchitectureOf: "x86_64")
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 1)

    let c2 = try XCTUnwrap(m[c.fallback[0]] as? ConditionalCompilation)
    assert(c2.condition, isArchitectureOf: "i386")
    XCTAssertEqual(c2.statements.count, 1)
    XCTAssertEqual(c2.fallback.count, 1)

    let c3 = try XCTUnwrap(m[c2.fallback[0]] as? ConditionalCompilation)
    assert(c3.condition, isArchitectureOf: "arm64")
    XCTAssertEqual(c3.statements.count, 1)
    XCTAssertEqual(c3.fallback.count, 1)

    let c4 = try XCTUnwrap(m[c3.fallback[0]] as? ConditionalCompilation)
    assert(c4.condition, isArchitectureOf: "arm")
    XCTAssertEqual(c4.statements.count, 1)
    XCTAssertEqual(c4.fallback.count, 1)
  }

  /// Tests the parsing of a conditional compilation statement with a `feature` condition.
  func testConditionalCompilationFeature() throws {
    let input =
      """
      #if feature(useLibC)
      foo()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    assert(c.condition, isFeatureOf: "useLibC")
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)
  }

  /// Tests the parsing of a conditional compilation statement with a `compiler` condition.
  func testConditionalCompilationCompiler() throws {
    let input = """
      #if compiler(hc)
      foo()
      #else
      awgr()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    assert(c.condition, isCompilerOf: "hc")
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)  // Body not parsed
  }

  /// Tests the parsing of a conditional compilation statement with a `compiler_version`
  /// greater-or-equal condition.
  func testConditionalCompilationCompilerVersionGreater() throws {
    let input = """
      #if compiler_version(>= 0 . 1)
      foo()
      #else
      awgr()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .compilerVersion(
        comparison: .greaterOrEqual(SemanticVersion(major: 0, minor: 1, patch: 0))))
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)  // Body not parsed
  }

  /// Tests the parsing of a conditional compilation statement with a `compiler_version`
  /// less-than condition.
  func testConditionalCompilationCompilerVersionLess() throws {
    let input = """
      #if compiler_version(< 100 . 1 . 2)
      foo()
      #else
      awgr()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .compilerVersion(
        comparison: .less(SemanticVersion(major: 100, minor: 1, patch: 2))))
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)  // Body not parsed
  }

  /// Tests the parsing of a conditional compilation statement with a `hylo_version`
  /// greater-or-equal condition.
  func testConditionalCompilationHyloVersionGreater() throws {
    let input = """
      #if hylo_version(>= 0 . 1)
      foo()
      #else
      awgr()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .hyloVersion(comparison: .greaterOrEqual(SemanticVersion(major: 0, minor: 1, patch: 0))))
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)  // Body not parsed
  }

  /// Tests the parsing of a conditional compilation statement with a `hylo_version`
  /// less-than condition.
  func testConditionalCompilationHyloVersionLess() throws {
    let input = """
      #if hylo_version(< 100 . 1 . 2)
      foo()
      #else
      awgr()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .hyloVersion(
        comparison: .less(SemanticVersion(major: 100, minor: 1, patch: 2))))
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)  // Body not parsed
  }

  /// Tests the parsing of disabled blocks in a conditional compilation statement.
  func testConditionalCompilationParsingInsideDisabledBlocks() throws {
    let input = """
      public fun main() {
        #if false
        <parse error>
        #endif
      }
      """
    let m = try testModule(contents: input)
    XCTAssertTrue(m.containsError)
  }

  /// Tests that parsing can be skipped for a `hylo_version` condition evaluating to `false`.
  func testConditionalCompilationParsingInsideVersionBlocks() throws {
    let input = """
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .hyloVersion(comparison: .less(SemanticVersion(major: 0, minor: 1, patch: 0))))
    XCTAssertEqual(c.statements.count, 0)  // Body not parsed
    XCTAssertEqual(c.fallback.count, 0)
  }

  /// Tests that parsing can be skipped over nested conditional compilation blocks.
  func testConditionalCompilationParsingSkipsParsingOverNestedBlocks() throws {
    let input = """
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #endif
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .hyloVersion(comparison: .less(SemanticVersion(major: 0, minor: 1, patch: 0))))
    XCTAssertEqual(c.statements.count, 0)  // Body not parsed
    XCTAssertEqual(c.fallback.count, 0)
  }

  /// Tests that parsing can be skipped over nested conditional compilation blocks, until `#elseif`.
  func testConditionalCompilationParsingSkipsParsingOverNestedBlocks2() throws {
    let input = """
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #endif
      #elseif os(bla)
      #endif
      """
    let (c, m) = try parseConditionalCompilation(input)
    XCTAssertEqual(c.statements.count, 0)  // Body not parsed
    XCTAssertEqual(c.fallback.count, 1)

    let c2 = try XCTUnwrap(m[c.fallback.first!] as? ConditionalCompilation)
    assert(c2.condition, isOsOf: "bla")
    XCTAssertEqual(c2.statements.count, 0)
    XCTAssertEqual(c2.fallback.count, 0)
  }

  /// Tests that parsing can be skipped in `#else` blocks.
  func testConditionalCompilationParsingSkipsParsingOverNestedBlocksInElse() throws {
    let input = """
      #if hylo_version(>= 0 . 1)
      #else
      <don't show parse error here>
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #endif
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .hyloVersion(comparison: .greaterOrEqual(SemanticVersion(major: 0, minor: 1, patch: 0))))
    XCTAssertEqual(c.statements.count, 0)  // Body not parsed
    XCTAssertEqual(c.fallback.count, 0)
  }

  /// Tests that parsing can be skipped over nested conditional compilation blocks in `#else` blocks.
  func testConditionalCompilationParsingSkipsParsingOverNestedBlocksInElse2() throws {
    let input = """
      #if hylo_version(>= 0 . 1)
      #elseif compiler_version(>= 0 . 1)
      <don't show parse error here>
      #if hylo_version(< 0 . 1)
      <don't show parse error here>
      #endif
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(
      c.condition,
      .hyloVersion(comparison: .greaterOrEqual(SemanticVersion(major: 0, minor: 1, patch: 0))))
    XCTAssertEqual(c.statements.count, 0)
    XCTAssertEqual(c.fallback.count, 0)
  }

  /// Tests that parsing is not skipped in `os` conditions.
  func testConditionalCompilationChecksParsing() throws {
    let input = """
      public fun main() {
        #if os(abracadabra)
        <expecting error here>
        #endif
      }
      """
    let m = try testModule(contents: input)
    XCTAssertTrue(m.containsError)
  }

  /// Tests parsing in negated `os` conditions.
  func testConditionalCompilationNotOperatorOnFalse() throws {
    let input = """
      #if !os(abracadabra)
      foo()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    // We should expand to the body of the #if
    XCTAssertEqual(c.expansion(for: ConditionalCompilationFactors()).count, 1)
  }

  /// Tests parsing in negated `true` conditions.
  func testConditionalCompilationNotOperatorOnTrue() throws {
    let input = """
      #if !true
      foo()
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    // We should expand to nothing.
    XCTAssertEqual(c.expansion(for: ConditionalCompilationFactors()).count, 0)
  }

  /// Tests conditional compilation with double negation.
  func testConditionalCompilationNotNot() throws {
    let input = """
        #if ! !true
        foo()
        #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    // We should expand to the body.
    XCTAssertEqual(c.expansion(for: ConditionalCompilationFactors()).count, 1)
  }

  /// Tests that parsing can be skipped after a negation in a conditional compilation statement.
  func testConditionalCompilationSkipParsingAfterNot() throws {
    let input = """
      #if !compiler_version(< 0 . 1)
      foo()
      #else
      <won't parse>
      #endif
      """
    let (c, _) = try parseConditionalCompilation(input)
    XCTAssertEqual(c.statements.count, 1)
    XCTAssertEqual(c.fallback.count, 0)  // don't parse the #else part
  }

  /// Tests the parsing of a conditional compilation statement with complex infix conditions.
  func testConditionalCompilationInfix() throws {
    let input = """
      #if os(macOS) || os(Linux) && hylo_version(< 1 . 0 . 0) || os(Windows)
      do_something()
      #endif
      """

    let (c, _) = try parseConditionalCompilation(input)
    guard case .or(
      .or(
        .operatingSystem(let os1),
        .and(
          .operatingSystem(let os2),
          .hyloVersion(comparison: .less(SemanticVersion(major: 1, minor: 0, patch: 0))))),
      .operatingSystem(let os3)) = c.condition else {
      XCTFail("Expected a complex infix condition")
      return
    }
    XCTAssertEqual(os1.value, "macOS")
    XCTAssertEqual(os2.value, "Linux")
    XCTAssertEqual(os3.value, "Windows")
  }

  /// Parses `input` as a conditional compilation statement.
  ///
  /// Returns the corresponding `ConditionalCompilation` and the module it was parsed in.
  func parseConditionalCompilation(
    _ input: String, file: StaticString = #filePath, line: UInt = #line
  ) throws -> (ConditionalCompilation, Module) {
    let contents = """
      public fun main() {
      \(input)
      }
      """
    let m = try testModule(contents: contents)
    XCTAssertFalse(
      m.containsError, "Parsing failed with error: \(m.diagnostics)", file: file, line: line)
    let body = try bodyOfFirstFunction(m)
    XCTAssertEqual(body.count, 1)
    let c = try XCTUnwrap(
      m[body[0]] as? ConditionalCompilation, "Expected a conditional compilation statement",
      file: file, line: line)
    return (c, m)
  }

  /// Asserts that `c` is an `os` condition with the given operating system name.
  func assert(
    _ c: ConditionalCompilation.Condition, isOsOf n: String, file: StaticString = #filePath,
    line: UInt = #line
  ) {
    if case .operatingSystem(let os) = c {
      XCTAssertEqual(os.value, n, file: file, line: line)
    } else {
      XCTFail("Expected os(_) condition", file: file, line: line)
    }
  }

  /// Asserts that `c` is an `architecture` condition with the given architecture name.
  func assert(
    _ c: ConditionalCompilation.Condition, isArchitectureOf n: String,
    file: StaticString = #filePath, line: UInt = #line
  ) {
    if case .architecture(let a) = c {
      XCTAssertEqual(a.value, n, file: file, line: line)
    } else {
      XCTFail("Expected architecture(_) condition", file: file, line: line)
    }
  }

  /// Asserts that `c` is a `feature` condition with the given feature name.
  func assert(
    _ c: ConditionalCompilation.Condition, isFeatureOf n: String, file: StaticString = #filePath,
    line: UInt = #line
  ) {
    if case .feature(let f) = c {
      XCTAssertEqual(f.value, n, file: file, line: line)
    } else {
      XCTFail("Expected feature(_) condition", file: file, line: line)
    }
  }

  /// Asserts that `c` is a `compiler` condition with the given compiler name.
  func assert(
    _ c: ConditionalCompilation.Condition, isCompilerOf n: String, file: StaticString = #filePath,
    line: UInt = #line
  ) {
    if case .compiler(let t) = c {
      XCTAssertEqual(t.value, n, file: file, line: line)
    } else {
      XCTFail("Expected compiler(_) condition", file: file, line: line)
    }
  }

  // MARK: Utilities

  /// Returns a test module that contains `input` as a source file.
  func testModule(contents input: String) throws -> Module {
    let s = SourceFile(name: .local(URL(string: "file:///tmp/test.hylo")!), contents: input)
    var p = Program(allowPartialStandardLibrary: true)
    let m = p.demandModule(Module.Name("M0"))
    let r = p[m].addSource(s)
    XCTAssertTrue(r.inserted, "Failed to insert source into module")
    return p[m]
  }

  /// Returns the body of the first function in `m`.
  ///
  /// - Requires: the first top-level declaration in `m` is a function declaration.
  func bodyOfFirstFunction(_ m: Module) throws -> [StatementIdentity] {
    XCTAssertEqual(m.sources.count, 1, "Expected exactly one source")
    let s = m.sources.values.first!
    XCTAssertEqual(s.roots.count, 1, "Expected exactly one top-level declaration")
    let x = m[s.roots.first!]
    XCTAssertTrue(x is FunctionDeclaration, "Expected a function declaration")
    return (x as! FunctionDeclaration).body!
  }

}

import FormatFixups
import XCTest

final class TypeBodyBlankLinesTests: XCTestCase {

  func testInsertsBlankLinesInStructBody() {
    XCTAssertEqual(
      applyingConventionFixups(
        to: """
          struct S {
            let x: Int
          }
          """),
      """
      struct S {

        let x: Int

      }
      """)
  }

  func testPreservesAlreadyPaddedBody() {
    let s = """
      struct S {

        let x: Int

      }
      """
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testIsIdempotent() {
    let once = applyingConventionFixups(
      to: """
        enum E {
          case a
        }
        """)
    XCTAssertEqual(applyingConventionFixups(to: once), once)
  }

  func testLeavesEmptyBodyAlone() {
    let s = "protocol Marker {}\n"
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testLeavesSingleLineBodyAlone() {
    let s = "struct S { let x: Int }\n"
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testLeavesFunctionBodiesAlone() {
    let s = """
      func f() -> Int {
        return 1
      }
      """
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

  func testPadsBeforeDocumentationOfFirstMember() {
    XCTAssertEqual(
      applyingConventionFixups(
        to: """
          extension S {
            /// The answer.
            var y: Int { 42 }
          }
          """),
      """
      extension S {

        /// The answer.
        var y: Int { 42 }

      }
      """)
  }

  func testPadsNestedTypeBodies() {
    XCTAssertEqual(
      applyingConventionFixups(
        to: """
          struct S {
            enum E {
              case a
            }
          }
          """),
      """
      struct S {

        enum E {

          case a

        }

      }
      """)
  }

  func testPadsOnlyMissingSide() {
    XCTAssertEqual(
      applyingConventionFixups(
        to: """
          struct S {

            let x: Int
          }
          """),
      """
      struct S {

        let x: Int

      }
      """)
  }

  func testReturnsInputWithParseErrorsUnchanged() {
    let s = "struct S {\n  let x:\n}\n"
    XCTAssertEqual(applyingConventionFixups(to: s), s)
  }

}

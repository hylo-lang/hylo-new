import Foundation
import HostUtilities
import Utilities
import XCTest

final class HostTests: XCTestCase {

  func testEnvironment() {
    XCTAssertNotNil(Host.environment["PATH"])
    XCTAssertNil(Host.environment["HYLO_SURELY_UNDEFINED_VARIABLE"])
    XCTAssertEqual(Host.environment["HYLO_SURELY_UNDEFINED_VARIABLE", default: "x"], "x")
  }

  func testEnvironmentCaseSensitivity() throws {
    #if os(Windows)
      XCTAssertEqual(Host.environment["pAtH"], Host.environment["PATH"])
    #else
      try XCTSkipIf(ProcessInfo.processInfo.environment["pAtH"] != nil)
      XCTAssertNil(Host.environment["pAtH"])
    #endif
  }

  func testForceWriteReadonly() throws {
    try FileManager.default.withUniqueTemporaryDirectory { (d) in
      let f = d.appendingPathComponent("a.txt")

      try "a".forceWriteReadonly(to: f, encoding: .utf8)
      XCTAssertEqual(try String(contentsOf: f, encoding: .utf8), "a")
      XCTAssertFalse(FileManager.default.isWritableFile(atPath: f.path))

      // Overwrites the file although it is read-only.
      try "b".forceWriteReadonly(to: f, encoding: .utf8)
      XCTAssertEqual(try String(contentsOf: f, encoding: .utf8), "b")
      XCTAssertFalse(FileManager.default.isWritableFile(atPath: f.path))
    }
  }

}

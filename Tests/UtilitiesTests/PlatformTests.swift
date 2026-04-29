import Foundation
import Utilities
import XCTest

final class PlatformTests: XCTestCase {

  func testArchitectureDescription() {
    XCTAssertEqual(Platform.Architecture.arm64.description, "arm64")
    XCTAssertEqual(Platform.Architecture.x86_64.description, "x86_64")
  }

  func testOperatingSystemDescription() {
    XCTAssertEqual(Platform.OperatingSystem.macOS.description, "macOS")
    XCTAssertEqual(Platform.OperatingSystem.linux.description, "Linux")
    XCTAssertEqual(Platform.OperatingSystem.windows.description, "Windows")
  }

}

import SwiftyLLVM
import LLVMWrapperCxx
import XCTest

class ExampleTest: XCTestCase {
  func testExample() {
    XCTAssertEqual(LLVM.LLVMContext.hellosd(), 42)
  }

}

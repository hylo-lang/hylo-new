// swift-tools-version:6.2
import PackageDescription

/// Settings common to all Swift targets.
let commonSwiftSettings: [SwiftSetting] = [
  .unsafeFlags(["-warnings-as-errors"])
]

let package = Package(
  name: "SwiftyLLVM",
  platforms: [
    .macOS(.v15)
  ],
  products: [
  ],
  targets: [
    .target(
      name: "LLVMWrapperCxx",
      swiftSettings: [.interoperabilityMode(.Cxx)]
    ),

    .target(
      name: "SwiftyLLVM",
      dependencies: ["LLVMWrapperCxx"],
      path: "Sources/LLVMWrapperSwift",
      swiftSettings: [.interoperabilityMode(.Cxx)]
    ),

    .testTarget(
      name: "SwiftyLLVMTests",
      dependencies: ["SwiftyLLVM"],
      swiftSettings: [.interoperabilityMode(.Cxx)]
    ),

  ],
  cxxLanguageStandard: .cxx20
)

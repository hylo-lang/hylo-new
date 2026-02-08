// swift-tools-version:6.2
import PackageDescription

#if os(Windows)
  let onWindows = true
#else
  let onWindows = false
#endif

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
    .executable(name: "bindgen", targets: ["LLVMWrapperGenerator"])
  ],
  dependencies: [
    .package(
      url: "https://github.com/tothambrus11/ClangSwift",
      revision: "c532386b460c34ffb0d34e721573cd1f754772bb"
    )
  ],
  targets: [
    .executableTarget(
      name: "LLVMWrapperGenerator",
      dependencies: [
        .product(name: "Clang", package: "ClangSwift")
      ]
    ),

    .systemLibrary(name: "SystemLLVM", pkgConfig: "llvm"),

    .target(
      name: "LLVMWrapperCxx",
      dependencies: ["SystemLLVM"],
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

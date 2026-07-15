// swift-tools-version:6.3
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
  name: "Hylo",
  platforms: [
    .macOS(.v26)
  ],
  products: [
    .executable(name: "hc", targets: ["hc"]),
    .executable(name: "hylo-demangle", targets: ["hylo-demangle"]),
    .library(name: "HyloStandardLibrary", targets: ["StandardLibrary"]),
    .library(name: "HyloFrontEnd", targets: ["FrontEnd"]),
  ],
  dependencies: [
    .package(
      url: "https://github.com/attaswift/BigInt.git",
      from: "5.7.0"),
    .package(
      url: "https://github.com/tothambrus11/Archivist.git",
      revision: "c7a5d710fbff1457e01cce0a207f1cb51c718189"),
    .package(
      url: "https://github.com/apple/swift-algorithms.git",
      from: "1.2.0"),
    .package(
      url: "https://github.com/apple/swift-argument-parser.git",
      from: "1.1.4"),
    .package(
      url: "https://github.com/apple/swift-collections.git",
      from: "1.1.0"),
    .package(path: "./Swifty-LLVM"),
  ],
  targets: [
    .executableTarget(
      name: "hc",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
        .product(name: "SwiftyLLVM", package: "Swifty-LLVM"),
      ],
      swiftSettings: commonSwiftSettings),

    .executableTarget(
      name: "hc-tests",
      dependencies: [
        .product(name: "ArgumentParser", package: "swift-argument-parser")
      ],
      swiftSettings: commonSwiftSettings),

    .executableTarget(
      name: "hylo-demangle",
      dependencies: [
        .target(name: "FrontEnd"),
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
      ],
      swiftSettings: commonSwiftSettings),

    .executableTarget(
      name: "hc-generate-stdlib",
      dependencies: [
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
        .target(name: "Utilities")
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "Driver",
      dependencies: [
        .target(name: "BackEnd"),
        .target(name: "FrontEnd"),
        .target(name: "StandardLibrary"),
        .target(name: "Utilities"),
        .product(name: "Archivist", package: "archivist"),
        .product(name: "SwiftyLLVM", package: "Swifty-LLVM"),
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "BackEnd",
      dependencies: [
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
        .product(name: "SwiftyLLVM", package: "Swifty-LLVM"),
      ],
      swiftSettings: commonSwiftSettings,
    ),

    .target(
      name: "FrontEnd",
      dependencies: [
        .target(name: "Utilities"),
        .target(name: "StableCollections"),
        .product(name: "Archivist", package: "archivist"),
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
        .product(name: "BigInt", package: "BigInt"),
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "StableCollections",
      dependencies: [
        .target(name: "Utilities")
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "StandardLibrary",
      path: "StandardLibrary",
      resources: [.copy("Sources")],
      swiftSettings: commonSwiftSettings,
      plugins: ["GenerateStandardLibraryPlugin"]),

    .target(
      name: "Utilities",
      dependencies: [
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "Interpreter",
      dependencies: [
        "FrontEnd",
        .product(name: "Collections", package: "swift-collections"),
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "CompilerTests",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "StandardLibrary"),
        .target(name: "Utilities"),
      ],
      exclude: ["negative", "positive", "README.md"],
      swiftSettings: commonSwiftSettings,
      plugins: ["CompilerTestsPlugin"]),

    .testTarget(
      name: "FrontEndTests",
      dependencies: [
        .target(name: "FrontEnd"),
        .target(name: "StandardLibrary"),
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "BackEndTests",
      dependencies: [
        .target(name: "BackEnd"),
        .target(name: "Driver")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "RuntimeTests",
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "StableCollectionsTests",
      dependencies: [
        .target(name: "StableCollections")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "UtilitiesTests",
      dependencies: [
        .target(name: "Utilities")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "InterpreterTests",
      dependencies: [
        "Interpreter", "FrontEnd",
      ],
      resources: [
        .copy("InterpreterTestPrograms")
      ],
      swiftSettings: commonSwiftSettings),

    .plugin(
      name: "CompilerTestsPlugin",
      capability: .buildTool(),
      dependencies: [
        .target(name: "hc-tests"),
      ],
      packageAccess: true),

    .plugin(
      name: "GenerateStandardLibraryPlugin",
      capability: .buildTool(),
      dependencies: [
        .target(name: "hc-generate-stdlib"),
      ]),
  ])

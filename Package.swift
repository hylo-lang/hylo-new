// swift-tools-version:6.1
import PackageDescription

#if os(Windows)
  let onWindows = true
#else
  let onWindows = false
#endif

/// Swttings common to all Swift targets.
let commonSwiftSettings: [SwiftSetting] = [
  .unsafeFlags(["-warnings-as-errors"])
]

let package = Package(
  name: "Hylo",
  platforms: [
    .macOS(.v13)
  ],
  products: [
    .executable(name: "hc", targets: ["hc"])
  ],
  dependencies: [
    .package(
      url: "https://github.com/kyouko-taiga/archivist.git",
      branch: "main"),
    .package(
      url: "https://github.com/apple/swift-algorithms.git",
      from: "1.2.0"),
    .package(
      url: "https://github.com/apple/swift-argument-parser.git",
      from: "1.1.4"),
    .package(
      url: "https://github.com/apple/swift-collections.git",
      from: "1.1.0"),
  ],
  targets: [
    .executableTarget(
      name: "hc",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
      ],
      swiftSettings: commonSwiftSettings),

    .executableTarget(
      name: "hc-tests",
      dependencies: [
        .product(name: "ArgumentParser", package: "swift-argument-parser")
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "Driver",
      dependencies: [
        .target(name: "FrontEnd"),
        .target(name: "StandardLibrary"),
        .target(name: "Utilities"),
        .product(name: "Archivist", package: "archivist"),
      ],
      swiftSettings: commonSwiftSettings),

    .target(
      name: "FrontEnd",
      dependencies: [
        .target(name: "Utilities"),
        .target(name: "StableCollections"),
        .product(name: "Archivist", package: "archivist"),
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
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
      swiftSettings: commonSwiftSettings),

    .target(
      name: "Utilities",
      dependencies: [
        .product(name: "Algorithms", package: "swift-algorithms")
      ],
      swiftSettings: commonSwiftSettings),

    .testTarget(
      name: "CompilerTests",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
      ],
      exclude: ["negative", "positive", "README.md"],
      swiftSettings: commonSwiftSettings,
      plugins: ["CompilerTestsPlugin"]),

    .testTarget(
      name: "FrontEndTests",
      dependencies: [
        .target(name: "FrontEnd")
      ],
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

    .plugin(
      name: "CompilerTestsPlugin",
      capability: .buildTool(),
      dependencies: [
        .target(name: "hc-tests")
      ]),
  ])

# HyloSwiftFormatter

`hylo-format` formats the repository's Swift sources according to the
[coding guidelines](../../CONTRIBUTING.md). It works in two steps:

1. It runs [`swift-format`](https://github.com/swiftlang/swift-format) (bundled with the Swift
   toolchain) using the configuration in `.swift-format.json` at the root of the repository. This
   handles indentation, the 100-column line limit, comment spacing, and the guideline-derived
   lint rules that `swift-format` supports.
2. It applies the `FormatFixups` rewriters, which implement the conventions of our style guide
   that `swift-format` cannot express:
   - a blank line after the opening brace and before the closing brace of the multiline body of a
     type, extension, or protocol declaration;
   - parentheses around the parameters of closures naming at least one parameter, e.g.
     `{ (e) in ... }` rather than `{ e in ... }`.

Formatting is computed on temporary copies of the sources, so files are rewritten only once a
whole file has been formatted successfully. A file whose rewrite would introduce a parse error is
left unchanged.

## Usage

From the repository root:

```sh
Tools/format.sh            # rewrites nonconforming files in place
Tools/format.sh --check    # reports nonconforming files; exits nonzero if there are any (CI)
Tools/format.sh Sources    # formats only the given paths
```

With no paths, the formatter processes `Package.swift`, `Plugins`, `Sources`, `Tests`, and
`Tools`. The Swifty-LLVM submodule is not formatted.

`swift-format` must be on the `PATH`; it ships with Swift 6 toolchains.

## Adding conventions

Conventions expressible in `swift-format`'s configuration belong in `.swift-format.json`. The
others are implemented as `SwiftSyntax` rewriters in `Sources/FormatFixups`, composed in
`applyingConventionFixups(to:)`, and covered by tests in `Tests/FormatFixupsTests`. Rewriters
must be idempotent and must only produce output that parses without errors.

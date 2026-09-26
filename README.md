# The Hylo Language

[![codecov](https://codecov.io/github/hylo-lang/hylo-new/graph/badge.svg?token=2auHoqmMSq)](https://codecov.io/github/hylo-lang/hylo-new)

Hylo is a safe systems programming language leveraging mutable value semantics and generic programming. To learn more, 
visit https://hylo-lang.org/.

## Building Instructions

The Hylo compiler is written in Swift, links against [LLVM 23](https://github.com/hylo-lang/llvm-build), and can be
built using the Swift Package Manager from the Swift 6.3.2 toolchain or later. For detailed setup instructions,
see [Building Instructions](https://hylo-lang.org/docs/contributing/building-the-compiler/) on our website.

## The Hylo Compiler's Runtime Dependencies
`hc` uses `clang` for linking, resolving them from PATH. On macOS, you will need `xcrun` 
on PATH so the compiler can find the SDK.

## Environment Variables

- `HYLO_DEFAULT_CACHE_ROOT`: the directory in which `hc` saves its module cache by default.
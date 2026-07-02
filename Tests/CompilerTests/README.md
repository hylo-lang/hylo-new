# Compiler tests

This directory contains tests running the entire compiler on program inputs.
Test suites are generated with the contents of the `negative` and `positive` sub-directories, which define use cases.
A use case is either a single Hylo source file or a directory representing a package.

A single-file test is compiled to a binary executable, just as if it was passed as an argument to `hc`.
A package test is built according to the configuration specified by its manifest.


## Testing without the standard library

You can add `//! no-std` on the first line of a single-file test to disable the loading of the standard library. We encourage using `no-std` when possible, as it makes the test significantly faster.

## Stopping after a compilation stage

Add `//! stage:stage_name` to stop the driver after a specific compilation stage. Valid stages are:
- `stage:parsing`
- `stage:typing`
- `stage:lowering`
- `stage:llvm`
- `stage:execution` (default); applicable only in positive tests.

## Expectation types

### Exit status

Specify an expected exit code by `exit-status:42` manifest attribute. `0` is expected by default.
Asserted when `stage` is set to `execution` (default). 

### Textual Artifact Expectations

Add a `test-case.<artifact-tag>.expected` file besides your `test-case.hylo` to assert the contents of a compilation artifact. Valid artifacts are:
- `*.raw-ir.expected`
- `*.refined-ir.expected`
- `*.llvm-ir.expected`

An artifact is composed of a set of contiguous sections, delimited by empty lines. E.g. each function in Hylo IR and LLVM IR are their own sections.

It is sufficient to specify a subset of sections of the actual artifact. The expected section is matched with the observed section having the closest first line. Then they are compared for equality.

## Inspecting Intermediate Artifacts

Intermediate compilation artifacts are saved on test failure as `*.observed` files besides the corresponding test case. You can temporarily set `alwaysSaveArtifacts` to `true` in `CompilerTests.swift` to save these even when a test passes.

## Generating Swift tests manually

Test cases are generated automatically as part of SPM's build sequence.
You can also use `hc-tests` to generate test cases manually.
The tool goes over each file or sub-directory under `negative` and `positive` and create a corresponding method to invoke `CompilerTests.compile(_:)`.

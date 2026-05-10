# Copy Windows DLL dependencies

Reusable composite GitHub Action that copies all DLLs required to run a given
Windows executable into the same directory (or any chosen destination), so the
result is portable to a fresh Windows machine that has neither the Swift
toolchain nor the Visual C++ runtime installed.

The action:

1. Runs `dumpbin /DEPENDENTS` on the executable.
2. For every dependency:
   - If a DLL of the same name is sitting next to the executable, it is treated
     as a build product and copied unconditionally.
   - Otherwise the dependency is only copied when it appears on a built-in
     allow-list of Swift, Foundation, libdispatch and MSVC runtime DLLs (which
     can be extended via the `extra-allowlist` input). DLLs that are not on the
     allow-list are assumed to be Windows system DLLs and are skipped.
3. Recurses into every copied DLL so transitive dependencies are bundled too.
4. Copies any matching `.pdb` files alongside their DLLs when present.

The resolution and allow-list logic is a direct port of
[`GenericWindowsBundler.swift`](https://github.com/moreSwift/swift-bundler/blob/main/Sources/SwiftBundler/Bundler/GenericWindowsBundler.swift)
from `moreSwift/swift-bundler`.

## Requirements

- Must be run on a Windows runner.
- `dumpbin` (from MSVC) must be on `PATH`. Use
  [`compnerd/gha-setup-vsdevenv`](https://github.com/compnerd/gha-setup-vsdevenv)
  earlier in the job to enter a Visual Studio Developer environment.

## Inputs

| Input | Required | Description |
|---|---|---|
| `executable` | yes | Absolute path to the `.exe` whose dependencies should be bundled. |
| `destination` | no | Directory to copy DLLs into. Defaults to the directory of the executable. |
| `extra-allowlist` | no | Newline- or comma-separated list of additional DLL base-names (with or without `.dll`) to allow copying from `PATH`. |
| `fail-on-unresolved` | no | `true` (default) to fail when an allow-listed DLL cannot be located on `PATH`; `false` to only warn. |

## Example

```yaml
- uses: compnerd/gha-setup-vsdevenv@main

- name: Build
  run: swift build -c release --product hc
  shell: pwsh

- name: Bundle DLLs next to hc.exe
  uses: ./.github/actions/copy-windows-dlls
  with:
    executable: ${{ github.workspace }}\.build\release\hc.exe
```

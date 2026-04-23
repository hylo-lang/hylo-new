## Release Workflow
Release drafts are created whenever pushing to a tag in the repository. You can manually
publish a release when editing the draft.

The conventional tag name for releases is `vX.Y.Z`, with an optional suffix for pre-releases (like `v0.0.2-test-lsp`).
The release workflow only triggers for a pattern matching `v*`.


## Spell Check
Spell checking is performed by [`typos`](https://github.com/crate-ci/typos) in this repository.
To run it locally, install `typos` from its [prebuilt releases](https://github.com/crate-ci/typos/releases), then use:

```sh
typos -c .typos.toml 
typos -c .typos.toml --write-changes
```

Repository-specific exclusions and allowlisted identifiers and words are defined in `.typos.toml`.

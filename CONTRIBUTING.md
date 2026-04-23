## Release Workflow
Release drafts are created whenever pushing to a tag in the repository. You can manually
publish a release when editing the draft.

The conventional tag name for releases is `vX.Y.Z`, with an optional suffix for pre-releases (like `v0.0.2-test-lsp`).
The release workflow only triggers for a pattern matching `v*`.

## Coding Conventions
Consult [CONVENTIONS.md](CONVENTIONS.md) for coding conventions used in this project.

## LLM usage
If you use an LLM to generate code, please disclose this in your Pull Request description.

While we embrace tools that improve efficiency, we must avoid committing code we do not understand. If your PR includes
LLM-generated code that is complex or opaque to you:

1. Stop
2. Understand and document what it is doing
3. Simplify it so that others can follow.

If you are unable to do these things, bring your problem up on Slack and work through a resolution with the community.

Ultimately, you are responsible for the code you commit. Ensure you review and test generated code thoroughly, and always alert reviewers to it.

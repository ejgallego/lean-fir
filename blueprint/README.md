# FIR compiler correctness Blueprint

This package records the selected W6 compiler argument, its assumptions and
open obligations. Start with the [compiler argument](FirBlueprint/Chapters/CompilerArgument.lean),
then the [formal catalog](FirBlueprint/Chapters/W6.lean) and
[development roadmap](FirBlueprint/Chapters/Roadmap.lean).

## Build

From the FIR root:

```sh
make blueprint
```

This prepares the official worktree-local Talos overlay and builds
`blueprint/_out/site/html-multi/index.html`. The package's checked-in toolchain
and manifests define its environment. For direct Lake commands, follow the
cache and scratch policy in [AGENTS.md](../AGENTS.md) and run from `blueprint/`.

The rendered reader entry is “The compiler argument: from a concrete call to
a theorem”. The [supporting-evidence section](FirBlueprint/Chapters/ProofScope.lean)
identifies dated audits and reproduction guides; this README and the checkout's
`AGENTS.md` provide operational instructions.
The build also generates source snapshots captured from associated module
paths during this build, including the Talos overlay, so declaration links
work without a published Git revision or a path into ignored working state.

The [VBP manual at the accepted package revision](https://github.com/leanprover/verso-blueprint/blob/19451b009e306e7436b82f4d9093c4d15f8cdfd8/doc/MANUAL.md)
and `lake exe vbp --help` document CLI and authoring features. A user-local
Codex skill is optional; it is not a contributor prerequisite.

## FIR authoring and review

The [proof policy and contribution chapter](FirBlueprint/Chapters/Contribution.lean)
owns the FIR-specific rules, reviewed statement identity, retained assumptions
and contribution packet. Draft targets live in `FirBlueprint/Targets/`;
production modules must never import them.

Follow [AGENTS.md](../AGENTS.md) for file ownership, coordination and integration.
The standing FIR root owns integration and package pins; W6 reviews its
mathematical claims. Source, trust and artifact evidence remain with their
production definitions and owner-maintained audits. The Blueprint distinguishes
checked associations, rough obligations and explicitly dated source evidence.

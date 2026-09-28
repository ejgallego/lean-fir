# FIR W6 Blueprint pilot

This is both a proof-development document and an evaluation of Verso Blueprint's
current dependency graph and frontier model. It starts with 24 substantive W6
nodes, including 18 associated with existing declarations and six open targets.
Read [EVALUATION.md](EVALUATION.md) for observed limitations and proposed
acceptance scenarios, and [CONTRIBUTING.md](CONTRIBUTING.md) for contribution
boundaries. No task is published to an external platform by this package.

## Build and inspect

From the FIR root:

```sh
make blueprint
```

This prepares the official worktree-local Talos RC2 overlay and builds the site
at `blueprint/_out/site/html-multi/index.html`. It does not change the production
proof package, toolchain or admission policy. The documentation package pins
Verso Blueprint and all resolved dependencies in its own manifest.

Before direct Lake commands, follow FIR's cache policy:

```sh
export LAKE_CACHE_DIR="$(bash scripts/fir-lake-cache-path.sh)" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export TMPDIR="$PWD/.deps/tmp"
cd blueprint
lake exe vbp discover
lake exe vbp query work-queue
lake exe vbp query node conditional-return
lake exe vbp query uses admission-closure
lake exe vbp query used-by heap-miss-closure
lake exe vbp build --serve
```

From `blueprint/`, use `lake exe vbp check` when inspecting a copied or persisted site.
The query JSON schema is currently unstable; the pilot does not introduce a
second registry or depend on a frozen export format.

## Authoring and ownership

Root owns this documentation experiment; W6 reviews mathematical claims and
contributor statements. The live W6 plan remains
[`integration/talos/PLAN.md`](../integration/talos/PLAN.md). The initial narrative
was reviewed against FIR `81bb0e2ab`; linked declarations are resolved from the
actual checkout at build time. Refresh the narrative when the proof boundary
changes, and identify the new reviewed commit.

`FirBlueprint/Chapters/W6.lean` contains the proof map. Existing results use
`lean` associations and inferred dependencies. Open targets have explicit
proposed proof dependencies. `bpref` links explain intended consumers without
inventing dependency edges. Unexpanded parts of the 20-branch audit remain
explicitly outside this overview's completeness claim.

Keep these dimensions distinct:

- formalization of the stated proposition;
- compiler obligations still exposed as hypotheses;
- execution/resource assumptions deliberately retained;
- transitive axioms checked by FIR's trust inventory;
- exact integration and validation evidence.

The Blueprint's built-in colors do not encode all five dimensions. Editorial
tags and prose describe the missing dimensions without pretending the tool
understands them. Planned statements have no fake Lean axioms or placeholder
proofs. The production source and compiled trust gates remain authoritative.

## Starter provenance

The skill-recommended `verso-templates --branch main blueprint` route failed
on 2026-09-28: templates main `15e1532c3ee2c9499474d280f1d6770bc127558c`
did not list a Blueprint template. As a maintainer experiment, this package
uses the minimal generator and package structure of Verso Blueprint's checked-in
`project_template` at `19451b009e306e7436b82f4d9093c4d15f8cdfd8`, adapted to FIR.
The dependency uses that immutable public commit, not a mutable local checkout.

# FIR lane coordination board

This is the portable coordination snapshot for parallel FIR work. The
integration owner is the only writer so the board cannot become a cross-branch
merge conflict. Lane owners send updates; the integration owner applies them
atomically. A harness-backed board may mirror this schema and become the live
view, while this file remains the repository handoff snapshot.

The board contains no executable policy. Separate Git worktrees provide the
actual isolation; this file only makes ownership, dependencies, and handoffs
visible. Add automation only after a repeated coordination failure gives it a
specific behavior to prevent.

Statuses are `active`, `ready`, `blocked`, `released`, or `parked`.

## Lane snapshot

Snapshot base: `main` at `373b0a9`.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `integration/wasm-lanes` | active | Split W6 proof and W7 generation topology | Agent/worktree contract |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | `elimDead` hygiene/machine relation | none reported |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Concrete retained-reuse capacity | W7 consumes current layout; no change reported |
| W7 generation | generation owner | `wasm/generation` | blocked | Resident allocator and styled `prettyM` package staged in rehearsal worktree | Waiting for this lane to be provisioned |
| Validation | validation owner | `validation/interpreter-corpus` | parked | Corpus is clean at snapshot base | none |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator and styled `prettyM` package | rehearsal only | `fcd11f3` plus later consumed W6 surfaces | staged | W6 owner after generation handoff | pending canonical build |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | active | this integration slice | Gives W6 and W7 independent branches and worktrees |

## Update format

Send one record per lane update:

```text
lane:
owner:
branch:
base:
head:
status:
slice:
contract-impact: none | <short description>
checks:
bug-cards: none | <IDs>
handoff/follow-up:
```

For a resident helper, also include:

```text
helper:
signature:
contract-base:
artifact-digest:
bridge-state: generation-ready | contract-proved | linked/accepted
```

The board reports coordination state; it does not replace clean worktrees,
tested commits, or the handoff requirements in `AGENTS.md`.

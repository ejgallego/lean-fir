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

Snapshot base: validation release candidate `bc688b6`, based on `main` at
`9cb483f`.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `integration/wasm-lanes` | active | Coordinate erased-reset consumers and independent W6/W7 handoffs | `RESET-ERASED-RELEASE` remains a consumer barrier |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | `elimDead` provenance checkpoint `9f24a07`; adapt reset simulation to `releaseResetField` | Consumes `RESET-ERASED-RELEASE` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | blocked | Concrete reuse-capacity and erased-reset refinements through `e12e55e` | `make talos-check` waits for the proof-owned reset simulation repair |
| W7 generation | generation owner | `wasm/generation` | active | Resident allocator and styled `prettyM` artifact committed at `cdfad5c`; acceptance handoff under review | New resident helper signatures queue a later W6 proof handoff |
| Validation | validation owner | `validation/interpreter-corpus` | released | Native-oracle erased reset/reuse fixture and coverage floor at `bc688b6` | Consumes and differentially checks `RESET-ERASED-RELEASE` |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator and styled `prettyM` package | `cdfad5c` | `9cb483f` | staged | W6 owner after generation handoff | pending checked handoff |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | active | `373b0a9` | Reset treats erased ownership slots as no-ops; validation is released, W6 is adapted, and the pass-proof reset simulation remains |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | active | `cdfad5c` | Generation checkpoint exists; exact artifact checks, digest, and concrete-host proof handoff remain |

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

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

Lane rows name their own landed commits; the board intentionally has no
moving global snapshot hash.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `integration/wasm-lanes` | active | Record the landed W7 allocator handoff and keep W6/W7 bridges explicit | No shared contract is blocking a lane |
| Lean pass proof | pass-proof owner | `proof/simpcase` | blocked | Compiler-derived binder-readiness endpoint is drafted in `ElimDeadMachineRel.lean`, but the uncommitted draft appeared alongside another owner's checkpoint | Ownership must be reconciled before proof edits, checks, or handoff continue |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Preserve mapped header capacity through leaf, fuel-indexed, recursive, and public ownership release | Consumes the released erased-reset contract; independent of W7 allocator and validation schemas |
| W7 generation | generation owner | `wasm/generation` | released | Resident allocator and styled `prettyM` package landed as `21f382c`; next generation slice may start independently | Allocator signatures queue a W6 Talos-adapter guard and later T5 bridge; no shared contract changed |
| Validation | validation owner | `validation/interpreter-corpus` | released | Mixed erased/owned reset release is observable through native and interpreter sharing state at `3b82b0b` | Differentially checks the released reset contract; no new shared contract |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator and styled `prettyM` package | `21f382c` | `2dfa1b3` | generation-ready | W6 owner at the later T5 bridge | styled Wasm `5134ef9811b1f80e17c1503afe6fd01e80a386ceace2e3eb6bd132509983f15e` |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | released | `373b0a9` | Reset treats erased ownership slots as no-ops; proof adaptation `8c2fff6`, W6 adaptation `afd7ab0`, and validation observation `3b82b0b` are landed |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | released | `21f382c` | Zero-import allocator and styled package are generation-ready; allocator installation preserves the current 177-import `prettyM` frontier, and W6 owns the later bridge proof |

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

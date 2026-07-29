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
| Integration | integration owner | `main` | active | Main is green through the kernel nullary-`.fap` counterexample and corrected semantic-admissibility endpoint `006ea2f`; the isolated `FLOAT-SCALAR-RUNTIME` producer remains ready at `c901e0d`, and its validation stack is rebased on current `main` through the carded tagged-float repair and 655-case checkpoint `bcbc1a9` | The validation stack exposes one exact pass-proof adaptation plus the already-recorded W6/W7 exhaustive consumers; all must be green before the shared contract and dependent fixtures land on `main` |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Complete exact machine dispatch, closed whole-program ownership/allocation fixtures, the kernel theorem that static well-formedness plus a successful run does not imply correctness, and `ElimDeadSemanticallyAdmissibleRun.loweringCorrect` are landed through `006ea2f`; the branch is aligned with `main` | No shared contract changed: whole-pass correctness now exposes runtime/ownership admissibility and foreign compatibility separately. The queued float-contract adaptation remains to extend `scalarFromType_ok_eq_immediate` with `float32` and `float` after rebasing onto validation contract commit `62de0d4` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Partial-closure capacity is proved at clean head `5095ac3`; the branch contains the stable closure-descriptor contract | W7 may consume the released descriptor table now; W6 remains the proof owner and rebases on current `main` before its next handoff |
| W7 generation | generation owner | `wasm/generation` | active | Resident cache publication, numeric operations, String operations, and fallbacks are landed through the zero-import `prettyM` checkpoint `071fcbc` | Uses released W6/W7 contracts; the owner must report the next generation helper and any new contract impact before handoff |
| Validation | validation owner | `validation/float-corpus` | active | Clean rebased head `bcbc1a9` records and fixes `FIR-BUG-impure-none-tagged-float-unbox`, adds tagged and heap boxing controls plus ten mixed float/object-layout projection and copy-on-write cases, and compares all 655 native and LCNF observations equal in evidence run `ee6a1eb3b06605e7b454c703895b6bd6b16a80665c60b51893faa4565c9bcfe0` | Runtime contract commit `62de0d4` adds tagged `float32`/`float` decoding. Root build, examples, 117 harness tests, 655-case validation, and nine direct-machine cases pass; the full gate stops only at the three queued W7 manifest matches, while the separate pass-proof cone has the one adaptation recorded above |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator, constructors, and styled `prettyM` through immediate Naturals | `64831f6` | `40f41c0` | generation-ready | W6 owner at the later contract bridge | styled Wasm `5d14b3fd2b1eb93de344ee69c6117e539eeed320c857248eb0fd4691b9d9e5d2` |
| Standalone immediate-Natural and UTF-8 String literals | `64831f6` | current W6 object layouts | generation-ready | W6 owner | Wasm `ab63fa578576748ff3ea8230986cf908d7285c54bc840bb60fec5fc7fa978473` |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | released | `373b0a9` | Reset treats erased ownership slots as no-ops; proof adaptation `8c2fff6`, W6 adaptation `afd7ab0`, and validation observation `3b82b0b` are landed |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | released | `21f382c` | Zero-import allocator and styled package are generation-ready; allocator installation preserves the current 177-import `prettyM` frontier, and W6 owns the later bridge proof |
| `W7-CLOSURE-DESCRIPTORS` | W7 | W6, W7, integration, artifact clients | released | `40f41c0` | Retains the duplicate-free capture-kind table after `partialApply` imports are removed, so closure header `aux3` remains stable; W6 must rebase before W7 consumes it in the resident closure allocator |
| `W7-RESIDENT-LITERALS` | W7 | W6, integration, artifact clients | released | `64831f6` | Adds a zero-import literal fixture, internalizes immediate Naturals in linked `prettyM`, retains Strings until their JavaScript consumers become resident, and advances text/styled checkpoints to 152/153 imports |
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `c901e0d`; extension `62de0d4` | Adds bit-exact `float32Bits`/`float64Bits`, typed validation schemas, LCNF codecs, and tagged `float32`/`float` unboxing. Card `FIR-BUG-impure-none-tagged-float-unbox` captures the native/LCNF discrepancy before repair; dependent head `bcbc1a9` now passes 655/655 comparisons with exact bits and mixed-layout ownership coverage. Pass proof must add two scalar cases to `scalarFromType_ok_eq_immediate` (the only focused-cone failure). W7 must extend exhaustive matches in `Fir/Wasm/Emit/Manifest.lean` at lines 149, 255, and 280; W6 must extend `Fir/Wasm/Concrete/HeapRefinement.lean` at lines 35, 116, and 136. After those adaptations rebase, integration can land the stack and activate compiler-generated Wasm/V8 raw-bit transport without overlapping W7 generation work. |

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

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
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, ledger-aware matching through boxes, and stack-safe resident String walkers through `0e1a564a`. Validation head `4b53a449` is rebased on that boundary and advances the ready stack to 673 native/LCNF cases with typed process supervision, real divergence, and real native source exits | Four isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, and process termination. The validation-only source-exit projection does not alter the canonical interpreter or request compiler work. The umbrella check remains gated by the queued `takeClosureApplication` proof consumers; the retained V8 rebuild is independently gated by W7's exhaustive float manifest cases |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Ledger-aware box matching is integrated at `7aac1f33` after the literal, constructor, and partial-application checkpoints; the working tree has an owned uncommitted `ElimDeadMachineRel.lean` continuation and is two main commits behind | Checkpoint the owned proof edit before rebasing. Continue with failed-token reuse, existing-address, and external-response branches, then assemble the unified ledger-aware dispatcher. Afterwards define the entry-indexed exact ownership invariant, adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172`, and prove the queued `takeClosureApplication` consumers |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Clean committed head `96778166` composes constructor-tag, object-field mutation, and erased-object-field correctness; it is two main commits behind | Extend the already-float-aware concrete relation with the missing exhaustive `HeapRefinement.lean` cases at 35, 116, and 136. Rebase before the next slice, then audit closure application against `takeClosureApplication`; W6 owns the concrete refinement, not the validation implementation |
| W7 generation | generation owner | `wasm/generation` | active | The stack-safe resident `prettyM` String walker and stress fixture are integrated on `main` at `7d9c1ad9` and `0e1a564a`; the clean generation branch is aligned with main | Add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280` in the next generation slice. The current retained V8 rebuild stops exactly at those three missing cases. Consume `processTermination` only when admitting a compiler-generated real-engine exit case; do not implement lane-4 source-exit projection in W7 |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `4b53a449`, based on `0e1a564a`, retains the earlier validation stack, types process supervision at `cada180b`, and compares real `lean_io_exit` statuses zero and seven at `4b53a449`. Run `b66c710673feb87f7a59cc7b4669e23688d4ed647fad6ecf4ecedb7e94f2a6f9` compares 673/673 observations equal; evidence `f8dfb5306f92a6ef655c9738590e6e3714e3ab9544b949f653587801d2a14df3` verifies offline | Shared contracts remain isolated at `4d1a830d`/`c6e8796a`, `8dff773f`, `4c1f1efc`, `13568541`, and `cada180b`. Harness tests are 126/126; index `cd004a8` composes 682 unique cases and 1844/1844 equal comparisons, 5948 interpreter steps, and 45/45 semantic floors. `FIR-BUG-validation-none-source-exit-terminal-outcome` was recorded before repair and is fixed. The retained 581-case V8 matrix verifies offline and intentionally excludes alias, panic, divergence, and source-exit cases. `make check` still stops only at the queued `takeClosureApplication` proof consumer in `AlphaEqvCode.lean:2209,2358-2360` |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `4d1a830d`; source-accurate extension `c6e8796a` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `c6e8796a` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `4b53a449` passes 673/673. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 must extend `HeapRefinement.lean:35,116,136`. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `8dff773f` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `4c1f1efc` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and now tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`, `effect-record-triply-aliased-byte-array-arguments`, and `effect-record-two-aliased-byte-array-groups`; W6 owns any later concrete refinement, not this validation implementation. |
| `NATIVE-TERMINATION-SUPERVISION` | integration/validation | native adapter, LCNF adapter, W7/V8, Talos runners | active | `13568541`; typed policy `cada180b` | Adds `timeoutMs` plus the backend-neutral `processTermination` enum: `protocol`, `timeoutDivergence`, or `sourceExit`. Native timeout is a typed backend timeout unless opted into divergence; ordinary nonzero status and signals remain crashes unless an exact source-exit fixture opts in, and signals always remain crashes. LCNF promotes only same-step, well-typed `Source.exitNat` terminal evidence under `sourceExit`, without changing the canonical interpreter result theorem. The divergence fixture at `52a99bf4` pins 256 steps; source-exit fixture `4b53a449` pins statuses zero/seven and one exact external step. Retained V8 evidence excludes both. W7 or Talos should consume this policy only when admitting corresponding real-engine cases; no compiler-side work is requested now. |

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

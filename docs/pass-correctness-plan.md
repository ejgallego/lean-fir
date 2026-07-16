# LCNF correctness and Wasm work plan

This is the repository's source of truth for implementation status and next
work. `docs/research.md` supplies rationale, while `docs/lcnf-to-c.md` supplies
the compiler-pipeline reference.

This is the executable work plan for the Lean 4.32.0 pipeline pinned by FIR.
It has two parallel directions sharing one semantic boundary:

```text
base LCNF ----> mono LCNF ----> final impure LCNF ----> direct C
                                         |
                                         +----> FIR semantics
                                         |
                                         +----> semantic Wasm ABI ----> Talos
```

The proof direction works backwards from final impure LCNF. The Wasm
direction works forwards from that same boundary. This lets the interpreter,
runtime model, differential examples, and bug reports serve both efforts.

## Why FIR represents three phases explicitly

Lean has three named LCNF phases but only two syntax purity indices:

| Phase | Underlying type | Principal invariant |
|---|---|---|
| base | `LCNF.Decl .pure` | polymorphic source structure remains |
| mono | `LCNF.Decl .pure` | polymorphism has been eliminated |
| impure | `LCNF.Decl .impure` | representation, effects, and ownership are explicit |

FIR does not duplicate the syntax. It defines `Program phase`, containing an
array of `LCNF.Decl phase.toPurity`. Consequently `BaseProgram` and
`MonoProgram` are distinct theorem inputs even though Lean represents both
with `.pure` declarations. `CheckedProgram phase` pairs a program with
`WellFormedAt phase`; the initial invariant is unique declaration names and
can be strengthened with facts from Lean's phase checker.

"Represent the phases explicitly" therefore means that phase boundaries and
invariants appear in types, not that FIR owns three AST implementations.

## Completed foundation

The following work is implemented and checked by the default build:

- Lean and all pipeline expectations are pinned to 4.32.0.
- `Fir.LeanIR` and `Fir.Wasm` are the consolidated public imports; executable
  examples and the legacy differential evaluator remain test-only modules.
- `Hygiene.lean` checks lexical variable/join-point scope and declaration-wide
  binder freshness for impure LCNF; `WellFormedAt .impure` carries this inherited
  compiler invariant, and the full interpreter corpus is a positive regression.
- `Pipeline.lean` checks every built-in pass key, occurrence, phase, and phase
  transition against `LCNF.builtinPassManager`.
- `Checkpoint.lean` can wrap Lean's actual `simpCase`, capture its input and
  output declaration groups, and is installed only by the inspection command.
- `Runtime.lean` models abstract Lean values, heap objects, reachable storage,
  ownership operations, reset/reuse, external effects, and observations.
- `Interpreter.lean` gives exhaustive final-impure instruction semantics,
  calls and closures, join points, a canonical small-step relation, an
  executable runner, and runner-to-relation soundness.
- `InterpreterExamples.lean` executes straight-line code, constructors and all
  projection classes, cases/defaults, direct and closure calls, joins,
  boxing, mutation, reference counts, deletion, both reuse paths, and typed
  externals.
- `make validate` compiles one shared source corpus through Lean's native
  backend and final impure LCNF, compares versioned structured observations,
  checks emitted-form coverage, and retains the exact compiler artifacts.
- `Inspect` remains a pass-checkpoint diagnostic; the original evaluator is a
  unit fixture rather than the semantic oracle.
- `PassCorrectness.lean` defines same-phase equivalence, cross-phase forward
  simulation, and impure observation equivalence modulo address renaming and
  unreachable heap garbage.
- `Passes/SimpCase.lean` proves internal-step prefix equivalence, selected-arm
  elimination, singleton default/constructor elimination, and removal of
  unreachable alternatives when the phase invariant selects a reachable arm.
  It also proves a generic selected-branch rewrite theorem and reduces default
  folding to the explicit semantic soundness obligation for `Code.alphaEqv`.
  `Passes/AlphaEqv.lean` relates alpha-renamed syntactic scopes to interpreter
  environments, proves related arguments and impure let values evaluate
  identically, and proves the binder-extension step once hygiene classifies new
  versus existing variables.
  `SimpCaseExamples.lean` checks the singleton, filtering, and genuinely
  alpha-renamed folding results against Lean 4.32's actual `simpCase.run`.
- `Fir.Wasm` defines the typed runtime ABI and exhaustively lowers impure LCNF
  to symbolic core-Wasm instructions and imports.
- `integration/talos` pins a Lean-4.32-compatible Talos revision, converts the
  symbolic module to Talos syntax, and executes a scalar module in Talos.
- `bugs/` supplies versioned discrepancy cards and a validator used by
  `make check`.

This is the semantic and engineering infrastructure for the campaign; it is
not a claim that Lean's individual compiler passes have all been proved
correct.

## Correctness statements

For a same-phase pass, correctness compares behavior at the entry points that
existed before the pass:

```text
Evaluates before entry args observation
    iff
Evaluates after entry args observation
```

Auxiliary declarations introduced by a pass are intentionally not new source
entry points. A proof may first establish forward simulation and use
determinism to obtain equivalence.

For `toMono` and `toImpure`, source and target values are not generally equal.
`LoweringCorrect` therefore accepts a `PhaseSimulation` with relations on
values and observations. The same pattern will relate impure observations to
Wasm observations.

Impure observations include the result or runtime fault, external world and
event trace, and reachable heap. Heap locations may be renamed and unreachable
cells may differ. This is the default equivalence for allocation-reordering,
reuse, and ownership passes.

Each compiler theorem has two layers:

1. prove a semantic transformation kernel correct;
2. prove that Lean's actual `CompilerM` implementation conforms to that
   kernel, including fresh names, declaration groups, and environment updates.

This separation keeps early semantic arguments legible without proving only
an unrelated reimplementation.

## Backward proof order

`reverseProofCampaign` constructs this order from the guarded forward pass
lists, so this document and the compiler cannot drift silently.

### 1. Final impure passes

1. `saveImpure`
2. `toposort`
3. final `inferVisibility`
4. `detectSimpleGround`
5. `pushProj` occurrence 1
6. `coalesceRc`
7. `expandResetReuse`
8. `explicitRc`
9. `explicitBoxing`
10. `inferBorrow`
11. `simpCase`
12. `elimDeadVars` occurrence 0
13. `resetReuse`
14. `pushProj` occurrence 0

The first three are primarily administrative. The first semantic case study
should be `simpCase`: it exercises control flow but not fresh heap layout.
Then prove projection movement and dead-value elimination. Ownership proofs
follow only after reachable-heap and reference-count invariants are stable;
the interpreter now provides the operational behavior needed for them.

### 2. Late mono and the impure boundary

1. `toImpure`
2. `extractClosed`
3. mono `inferVisibility`
4. `saveMono`
5. `cse` occurrence 2
6. `elimDeadBranches`
7. `simp` occurrence 5
8. `extendJoinPointContext` occurrence 1

`toImpure` needs the first substantial cross-phase value relation: mono
constructors and applications must correspond to concrete impure layouts,
closures, boxes, and projections.

### 3. SCC split and early mono

After proving the declaration-group SCC split, continue backwards through:

1. `lambdaLifting`
2. `floatLetIn` occurrence 2
3. `simp` occurrence 4
4. `commonJoinPointArgs`
5. `reduceArity`
6. `floatLetIn` occurrence 1
7. `extendJoinPointContext` occurrence 0
8. `structProjCases`
9. `reduceJpArity`
10. `simp` occurrence 3

These proofs require alpha-insensitive relations for generated declarations
and explicit treatment of original entry points.

### 4. Base phase and frontend lowering

Work backwards from `toMono` through the guarded base list and finish with
`toLCNF`. `toMono` introduces the base-to-mono value relation. Specialization,
lambda lifting, join-point discovery, and simplification should reuse the
declaration-renaming infrastructure developed for mono.

## Parallel Wasm track

The Wasm track proceeds independently where proof work does not yet depend on
an earlier LCNF phase:

1. freeze and test the `i32`/`i64` value ABI and the typed `fir.*` runtime
   operation signatures;
2. implement Talos host functions for allocation, projections, mutation,
   ownership, reset/reuse, closures, and external calls;
3. run every interpreter example through the FIR-to-Talos path and compare
   outcomes, worlds, traces, and reachable heaps;
4. prove instruction-level simulation, then lift it to functions and modules;
5. connect the theorem to compiler-produced final impure snapshots;
6. only then consider binary encoding or a production runtime ABI.

The core FIR build remains independent of Talos. This keeps AGPL licensing and
the external repository pin explicit and avoids making proof work depend on a
network checkout.

The validation track does not overlap this compiler work.  Once the Wasm track
provides an executable supported fragment and stable artifact/ABI handoff, the
validation runner will execute that artifact in V8 against the native Lean
oracle.  Talos then becomes another consumer of the same backend protocol and
is compared with V8 on identical modules and inputs.

## Differential checkpoints and bug cards

Every new pass theorem begins with a compiler-generated corpus and records:

- the guarded pass key and occurrence;
- source and target declarations at that checkpoint;
- source and target interpreter observations;
- the theorem or invariant being exercised;
- the exact command and Lean revision.

When a mismatch could indicate a compiler or model bug, copy
`bugs/_template.md` immediately and keep the card at `candidate` until it is
minimized. Classify it as `compiler`, `fir-semantics`, `wasm-adapter`, or
`upstream-drift`; link the eventual permanent regression before marking it
fixed. Workarounds belong in the card rather than silently weakening a theorem.

## Current `simpCase` proof

Two bounded proof slices are integrated. The first specifies and proves the
two rewrites that discard control-flow structure:

1. removing unreachable alternatives, under the explicit invariant that the
   runtime-selected arm is reachable;
2. eliminating a singleton default arm, or a singleton constructor arm whose
   tag invariant holds.

The second proves that an arbitrary case-table rewrite is correct whenever the
branches selected before and after the rewrite are semantically equivalent.
It defines `AlphaEqvSoundAt` as the exact missing bridge from Lean's Boolean
`Code.alphaEqv` test to that semantic equivalence, and proves default folding
correct conditional on this bridge. This exposes the remaining trust boundary
rather than treating alpha-equivalence as an unproved semantic fact.

The executable corpus runs Lean's actual pass on all three shapes and checks
that it produces the specification result. The folding fixture uses different
local `FVarId`s in its equal bodies, so it exercises alpha-renaming rather than
mere syntactic equality. No discrepancy was found.

Attempting to remove the `AlphaEqvSoundAt` hypothesis exposed a necessary
phase invariant. `Code.alphaEqv` accepts a minimized pair with different
observations when local `FVarId`s are reused. Lean's compiler intends these IDs
to be globally fresh. FIR now checks that invariant, along with lexical scope,
at the impure phase boundary. The executable witness, fix, and permanent
regression are recorded in `FIR-BUG-impure-simpCase-alpha-hygiene`; this was a
FIR invariant gap, not evidence of a compiler error on compiler-generated LCNF.

The first alpha-soundness layer is also integrated. It defines environment
coverage and agreement over Lean's right-to-left `FVarIdMap`, establishes the
identity base case, proves lookup and argument-array evaluation preservation,
and isolates binder extension behind the exact classification fact supplied by
`withFVar` plus hygiene.

The next semantic layer is integrated as well. `LetValueRelated` covers every
impure let-value constructor and records equality of all metadata observed by
the interpreter. `evalLetValue_eq_of_related` proves that related declarations
evaluate to the same action and runtime state under related environments. In
particular, declaration types remain an explicit premise because `unbox`
observes them, while Lean's executable checker establishes only type
alpha-equivalence.

The executable argument-array bridge is now proved in the completeness
direction: `eqvArgs_true_of_related` verifies that Lean's parallel Array/Subarray
loop returns `true` for every pointwise-related argument array. Its loop
invariant relates the unprocessed left suffix to the remaining right stream and
records that the reader map is unchanged. The converse direction, which
extracts the pointwise relation from a successful Boolean check, remains the
soundness obligation needed by the pass proof.

The remaining bounded work is:

1. derive binder classification from `withFVar` and hygiene, prove the
   soundness direction of Lean's executable argument checker, bridge the
   let-value checker to the semantic relation, and extend the simulation
   through recursive code to prove `Code.alphaEqv` sound;
2. connect `filterUnreachable`, `addDefaultAlt`, and `simplifyCases` directly
   to the local rewrite theorems, creating a bug card for every mismatch;
3. lift the resulting theorem through recursive code, declarations, and program
   entry evaluation;
4. expand the compiler-generated conformance corpus around the whole pass;
5. in parallel, continue the Talos runtime work and run
   the constructor/projection examples end to end.

Completing those items finishes the first whole-pass theorem and the first
non-scalar Wasm differential test without forcing either track to wait for the
other.

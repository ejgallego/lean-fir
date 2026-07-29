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
  versus existing variables. `Passes/AlphaEqvCode.lean` now carries that
  relation through terminal code, value bindings, saved bind frames, machine
  controls, states, core-step results, and impure case selection.
  `Passes/AlphaEqvLocal.lean` provides a total transparent copy of Lean 4.32's
  recursive checker, including a proof-facing structural alternative traversal;
  `Passes/AlphaEqvLocalSound.lean` proves local acceptance constructs the
  declarative relation for terminal code, value bindings, sequential impure
  effects, recursively nested deterministic case tables, join declarations,
  parameterized join bodies, and jumps under explicit normalization,
  well-formedness, and runtime-metadata premises;
  `Passes/AlphaEqvTrusted.lean` isolates correspondence with the opaque
  upstream checker behind one audited axiom.
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
minimized. Classify it as `compiler`, `fir-semantics`,
`validation-harness`, `wasm-adapter`, or `upstream-drift`; link the eventual
permanent regression before marking it fixed. Workarounds belong in the card
rather than silently weakening a theorem.

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

The executable argument-array bridge is now proved in both directions.
`eqvArgs_true_of_related` verifies that Lean's parallel Array/Subarray loop
returns `true` for every pointwise-related argument array, while
`argsRelated_of_eqvArgs_true` recovers the semantic relation from a successful
check when both arrays are lexically scoped. Their loop invariants respectively
track the unprocessed suffixes and the successfully checked prefix while
recording that the reader map is unchanged.

The executable let-value bridge is now proved too.
`letValueRelated_of_eqvLetValue_true` covers every impure constructor and uses
the argument soundness theorem for nested argument arrays.
`letDeclValueRelated_of_eqvLetValue_true` lifts that result to declarations.
Both the `.box` type and declaration result type remain exact premises: Lean's
checker establishes only type alpha-equivalence, while FIR's current runtime
semantics observes those types during boxing and unboxing. This isolates the
remaining type-level obligation instead of folding it into the recursive code
proof.

Binder extension is no longer an assumed classification boundary.
`AlphaEqvBind` proves the comparison laws needed to reason about Lean 4.32's
`Name.quickCmp`-backed `FVarIdMap`, then proves the concrete lookup law for
insertion and identifies `withFVar` with that right-to-left update.
`RenamingScoped` records that every mapped right-hand variable points into the
left scope; it holds for the empty map, is preserved by a fresh binder, and
yields the exact new-pair/old-pair split required by `envsAgree_bind`. Thus the
recursive simulation can extend both the renaming and runtime environments
without carrying an extra classification hypothesis.

The first recursive-code layer is integrated. `TerminalCodeRelated` covers
`return` and `unreach`, while `CodeRelated` adds recursive value bindings under
the same right-to-left renaming update as Lean's checker. `FrameRelated`,
`ControlRelated`, `MachineStateRelated`, and `CoreResultRelated` make the
one-step invariant explicit. `coreStep_code_related` covers faults and all
three successful let actions: immediate values extend both environments,
whereas named and value calls save the agreement, freshness, and continuation
relation in paired bind frames. `coreStep_yielded_bind_related` proves that a
returned call value pops those frames and resumes the related continuations
under the extended binders.

The sequential impure-code layer is integrated as well. `CodeRelated` now
covers object, usize, and scalar field writes, tag updates, reference-count
increments and decrements, and deletion. `runtimeEffectResult_related` factors
their common proof shape: related operands select one identical runtime
operation; faults yield one observation, while success enters related
continuations with the shared updated runtime. Persistent `inc` and `dec`
instructions take the matching no-op path. The `sset` type annotation is left
unconstrained in the semantic relation because the interpreter does not
observe it; relating Lean's type checker remains an executable-bridge concern.

The first branching layer is integrated. `AltRelated` relates constructor and
default bodies, while `CaseSelectionRelated` states that `chooseAlt` either
fails on both sides or selects related code. Structural lemmas lift this
relation through constructor lookup, default lookup, and their combined
selection rule. The `cases` branch of `coreStep_code_related` now covers
discriminator lookup faults, tag-reading faults, missing alternatives, and
successful entry into related branch bodies.

Case selection is now proved insensitive to table order under the exact
semantic condition it needs: each constructor tag and the default selector
determine at most one body. Successful and failed constructor/default lookups
are first characterized by table membership, then transported through
`List.Perm`; `chooseAlt_eq_of_perm` combines the two lookup results.
`QSortPerm` proves directly against Lean 4.32's private partition and sort
workers that `Array.qsort` returns a permutation. `sortAlts_perm` specializes
that generic theorem to Lean's alternative comparator. Consequently,
`CaseTableNormalizationInvariant` now contains only the genuine compiler-side
obligation—selector determinism—and `chooseAlt_sortAlts_eq` derives the
normalization permutation internally.

The older terminal boundary theorems remain useful independently:
`coreStep_terminal_related` proves matching immediate outcomes, and
`terminalCodeRelated_empty_sound` discharges both terminal cases at the
top-level semantic boundary. The proof also isolates the exact remaining
executable bridge in `alphaEqvSoundAt_of_terminal_bridge`.

Trying to prove that bridge exposed an upstream proof-interface blocker. Lean
4.32 declares recursive `LCNF.AlphaEqv.eqv` as an opaque `partial def` and
exports no safe equation theorem, so a successful `Code.alphaEqv` check cannot
be unfolded even for two `return` instructions.

FIR now ships `AlphaEqv.Local.eqv`, a total transparent fuel-indexed copy of
the full Lean 4.32 checker. `AlphaEqvLocalSound` defines
`CodeSideConditions`, containing lexical scope, binder freshness, and exact
runtime-observed type metadata not established by alpha-equivalence. Its
theorem `codeRelated_of_local_accepts` does not depend on FIR's trusted bridge
and proves that a successful local check constructs `CodeRelated` through
`return`, `unreach`, recursive value bindings, and every sequential
mutation/ownership instruction currently represented by that relation.
`CodeSideConditions.cases` is recursive: constructor/default side conditions
are indexed by semantic selector and may themselves contain cases beneath any
already-supported continuation constructor.
The local alternative loop is now a transparent list recursion after Lean's
normalizing sort. `altsRelated_of_local_check` proves that an accepting
ordered traversal constructs the semantic alternative relation, and
`codeRelated_of_local_accepts` uses its structural branch induction hypotheses
to lift that traversal through arbitrarily nested `cases` nodes. Branch side
conditions are indexed by constructor tag/default rather than array position,
so the proof can follow the checker's normalized traversal and then return to
the interpreter's original order. The earlier fixed-point/canonical-array
premise is gone; `CaseTableNormalizationInvariant` instead exposes only the
strictly weaker selector-determinism obligation, because normalization's
permutation property is now a theorem. The trusted adapter exposes the
matching compiler-facing case theorem. Proof regressions cover the empty-table
selection-failure path, a populated constructor/default table reordering, a
two-level normalized case relation, and rejection of mismatched nested
constructor/default bodies; executable guards compare each nested fixture with
the upstream checker.

The Lean 4.32 phase audit found no public invariant from which selector
determinism can be derived. The pure checker rejects duplicate constructor
names but assigns its `hasDefault` flag without consulting it, while impure
`Cases` contains an unrestricted alternative array and no preservation
theorem through `Alt.toImpure`. FIR therefore keeps
`CaseTableNormalizationInvariant` as the exact minimal phase bridge rather
than weakening semantic selection. The missing upstream proof interface and
duplicate-default check are recorded in
`FIR-BUG-impure-case-table-selector-determinism`.
`AlphaEqvTrusted` is opt-in and contains the sole project correspondence axiom:
upstream acceptance implies a finite accepting local run. The adapter records
the audited upstream source hash. `make check` rejects toolchain/source drift,
additional project axioms, or a `partial def` in the local checker, while
executable guards compare the two implementations over every impure code
constructor represented in the interpreter corpus. A Lean proof regression
also closes the genuinely alpha-renamed `let` fixture through
`CodeSideConditions`, local acceptance, and `CodeRelated`. The exact compiler
Boolean is therefore usable through a small, explicit trust boundary;
replacing that axiom with an upstream theorem remains the desired final
resolution. Details are recorded in
`FIR-BUG-impure-alphaEqv-opaque-eqv`.

The control-flow audit is now underway. Lean 4.32's pure checker establishes
that a jump target is an in-scope join point and that its argument count equals
the target arity, but `Decl.check` remains a no-op at the impure phase. FIR's
`ImpureHygienic` boundary preserves join/variable scope and global binder
uniqueness; its current `codeScoped` predicate does not separately record jump
arity. The transparent alpha checker nevertheless rejects unequal parameter
and argument counts. `Local.withParamsUsing` now exposes the parameter loop
and every reader-map extension instead of delegating to Lean's indexed loop.
`paramBodyRelated_of_local_check` proves that an accepted traversal constructs
a recursively related body under the accumulated parameter renaming, with
freshness supplied by the phase boundary. The first regression closes an
alpha-renamed one-parameter join body containing reordered constructor/default
cases. Named negative regressions reject mismatched join bodies, targets,
arities, and arguments; call regressions cover renamed call arguments and
reject target/argument mismatches. Every fixture is checked against the
upstream Boolean implementation. This slice introduces no new trusted axiom.

The declarative proof relations now distinguish lexical variable scope from
active join scope. `CodeRelated`, branch selection, controls, and machine
states carry paired left/right join-scope indices, and every already-proved
constructor preserves them unchanged. Top-level trusted theorems and
regressions instantiate both scopes with the empty list. `CodeRelated.jp` now
relates the parameterized body before extending the renaming and extends only
the continuation's active join scopes; `CodeRelated.jmp` requires an
alpha-related target present in both active join scopes and related,
variable-scoped arguments. `CodeSideConditions` records the matching freshness
and scope facts.

Local-checker soundness for this control-flow syntax is complete. The proof is
a fuel- and phase-indexed mutual recursion: recursive code checks consume fuel,
the empty parameter traversal enters code at the same fuel, and nonempty
parameter traversals decrease their list length. The full regression constructs
`CodeRelated` for an alpha-renamed `jp`, its normalized case body, a subsequent
value binding, and the final `jmp`.

Runtime join installation and invocation are now part of the simulation.
`JoinEnvsRelated` tracks alpha-renamed join stacks, their declaration bodies,
transport across ordinary variable binders, and dormant prefixes accumulated
after a declaration was installed. Related target lookup recovers the
declaration's historical variable/join scopes while retaining a certificate
for the complete current runtime stacks. Pointwise parameter binding then
extends both environments, both scope indices, and the renaming in lockstep.
`coreStep_code_related` proves both the `jp` and `jmp` steps, including equal
argument-evaluation faults, successful jumps into related bodies, and matching
arity-mismatch observations. Regressions execute both steps on the full
alpha-renamed join fixture. `CoreStepSupported` consequently covers every code
head represented by `CodeRelated`. The proof interface still states the
compiler's global-freshness consequence that variable and parameter binders
cannot shadow active join identifiers. No runtime contract or trusted
assumption changed.

Whole-control simulation is now complete at the interpreter's `coreStep`
boundary. Related yielded values pop bind, apply, and cache frames in lockstep;
cache writes preserve equal runtimes. Named calls agree on global-cache lookup,
partial-application allocation, argument splitting, parameter binding,
extra-argument frames, internal code entry, external requests, and faults.
Closure calls read the same heap cell and delegate to the named-call theorem.
`coreStep_machine_related` combines those paths with the complete code-head
simulation. Focused regressions enter the same one-parameter body through both
a named call and a heap closure.

Declaration entry adds one deliberate phase premise: `ProgramBodiesRelated`
says that every reachable internal declaration is reflexively related beneath
its parameter binders. This is not a new axiom; call proofs accept it as an
ordinary proposition. Attempting to derive it exposed a FIR proof-interface
bug: `ImpureHygiene.codeScoped`, its alternative/declaration helpers, and the
global binder traversals are opaque `partial def`s. The kernel cannot invert
even an accepted `.return` check, so the checked impure program boundary cannot
yet supply the scope and freshness facts required by `ProgramBodiesRelated`.
`FIR-BUG-impure-none-opaque-hygiene` records the minimal failure and the
required transparent-total refactor. The semantic proof keeps the exact
ordinary premise instead of adding another axiom or weakening its invariant.

The simulation now crosses the relational small-step boundary. A complete
case proof shows that every `coreStep` result preserves the immutable program;
the result is lifted through internal steps, external waiting/resumption, and
finite executions. `step_forward` matches one left step with one right step,
using the same external response after transporting equal runtimes.
`steps_forward` composes this into a same-length execution while transporting
`ProgramBodiesRelated` across successor states. `evaluatesState_forward` then
reproduces every terminating observation, and `diverges_forward` reproduces
arbitrarily long executions. The declaration-entry fixture exercises the
execution-level interface. `StatesBisimilar` packages independently indexed
simulations in both alpha-renaming directions; from it,
`evaluatesState_iff_of_bisimilar` proves observational equivalence for every
terminating result and `diverges_iff_of_bisimilar` proves divergence
equivalence. This slice adds no trusted assumption.

The bidirectional checker boundary is connected too.
`codeEquivalentAt_of_birelated` embeds two oppositely oriented `CodeRelated`
proofs into related machine states whenever the environment covers the proof
scope, the saved frames relate to themselves, and declaration bodies satisfy
the explicit phase premise. `codeEquivalentAt_of_local_accepts_both` obtains
those two relations from FIR's transparent checker and the two orientations of
`CodeSideConditions`; it is axiom-free. The genuinely alpha-renamed `let`
fixture now closes all the way to `CodeEquivalentAt`. The compiler-facing
`trustedCodeEquivalentAt_of_upstream_both` converts the two Lean Boolean
checks through the existing audited correspondence axiom. It adds no trusted
assumption and deliberately does not assume checker symmetry.

`SimpCaseCorrectness` now specializes that boundary to the pass's
alpha-equivalent default folding. The axiom-free theorem consumes two local
checker acceptances; the compiler-facing theorem consumes both Lean Boolean
checks and reuses the sole audited correspondence bridge. A regression proves
the real `foldAlphaEquivalent` fixture observationally equivalent at the
`True` constructor tag, exactly where `alphaRight` is replaced by
`alphaLeft`. The existing command regression still executes Lean's actual
pass and confirms the resulting syntax.

All three local rewrite families expose `CodeEquivalentAt` interfaces. The
singleton-default fixture eliminates directly; the unreachable-filter fixture
first proves the compiler-shape dead arm removable and then eliminates the
surviving singleton constructor; the alpha-fold fixture uses the bidirectional
checker theorem. Thus every original actual-pass fixture has both an executed
syntax regression and a kernel-checked observational-equivalence proof at its
valid runtime tag.

The execution relation also supports passes whose machines do not advance in
lockstep. `NonLockstep.Reaches` existentially hides a finite target step count,
and `StutteringSimulation` allows one source step to match zero or more target
steps while preserving a caller-chosen machine relation. Two such simulations
form a `StutteringBisimulation`, which proves equivalence of every terminating
observation without requiring equal programs or equal step counts.
`SamePhaseCorrectOn`, `InitialInvariantOn`, and `MachineRelatedWith` expose the
typed/admissible entry boundary required by control-flow simplifications.

### Consolidated whole-program `simpCase` endpoint

The initially missing recursive compiler graph is now represented locally.
`SimpCaseCompilerBridge.shadowCode?` is a transparent, fuel-indexed copy of
the output-producing portion of Lean 4.32's private traversal. It recursively
covers every impure code constructor and deliberately omits only compiler
bookkeeping calls that do not affect returned syntax. `shadowProgram?` lifts
that traversal through declarations and programs. `checkActualAgreement`
executes the pinned upstream pass and the shadow on the same input and rejects
any returned-syntax mismatch.

`SimpCaseScopedBridge` composes structural traversal, alpha-equivalent branch
folding, and structural traversal again. Its
`ScopedProgramPhaseEndpointCertifiedTrace` carries the recursive source and
target certificates needed by the semantic relation.
`SimpCaseWellFormed.ProgramWellFormed` packages:

- the shared impure phase invariant;
- the transparent scope check;
- deterministic case-table normalization;
- canonical runtime-observed type metadata.

The preferred theorem
`shadowProgram_samePhaseCorrectOn_reachableCaseTag_of_programWellFormed`
takes that well-formedness package, a successful transparent run, and an
`UpstreamBridge`, then returns `SamePhaseCorrectOn` for the trace's explicit
admissible entry arguments. This is the first assembled whole-program
`simpCase` theorem for the transparent executable traversal.

Two boundaries remain explicit:

1. Lean 4.32 keeps the actual recursive traversal and its case simplifiers
   private/opaque. Actual-pass agreement is therefore executable,
   source-hash-guarded evidence rather than a universal kernel equation.
   `FIR-BUG-impure-simpCase-private-proof-interface` records the missing public
   equation/graph interface.
2. The compiler-facing alpha-equivalence specialization instantiates
   `UpstreamBridge` with the single audited
   `AlphaEqvTrusted.lean432UpstreamBridge` axiom. The transparent local-checker
   soundness theorems themselves remain axiom-free.

## Current `elimDeadVars` proof

`elimDeadVars` is the active proof lane after `simpCase`. It requires a
reachability-aware relation because deleting an unused allocation changes the
raw heap while preserving every observable root.

### Transparent compiler graph and static certificates

`ElimDead.shadowCode?` is an audited, fuel-indexed copy of Lean 4.32's impure
backwards liveness/elimination traversal. It records the final used-local set,
retained/deleted let decisions, retained/deleted join decisions, and
retained/deleted write decisions. The traversal lifts through declaration
groups and whole programs.

`ExactShadowCodeGraph` and `ExactShadowCodeView` retain the proof-relevant
branch selected by that run. The hygiene layer proves:

- lexical scope and canonical binder uniqueness for every code subtree;
- absence of every deleted binder from the ambient live set;
- hereditary exact provenance for live join bodies, saved continuations,
  declaration bodies, and active code;
- projection of that exact provenance to the monotone operational graph.

`ProgramElimDeadWellFormed` combines the shared `ProgramWellFormed` package
with transparent binder uniqueness. A successful `shadowProgram?` run then
constructs `ProgramRelated (BinderReadyShadowCodeRelated fuel)`.

### Reachable-runtime simulation

`ShadowRuntimeRel` compares only heap cells reachable from published roots,
modulo an injective partial address renaming. Unreachable source garbage may
therefore be absent from the target. The machine relation carries:

- related live environments and join tables;
- related declaration bodies and saved frames;
- reference-count, persistence, cache, reset/reuse, and runtime-fault facts;
- related external requests and suspended machines.

The operational dispatcher `match_codeStep_of_ready` covers every executable
impure code constructor and all fourteen impure let-value families. Deleted
nodes take a source-only step; retained nodes advance together, possibly
extending the address renaming. Terminal faults and returned observations are
covered separately. `ReachableMachineRelatedWith.simulation` lifts these
local results to a finite-stuttering forward simulation.

At program level, `shadowProgram_loweringCorrect_reachablyCodeReady` proves
`LoweringCorrect` for a successful transparent `elimDeadVars` run from:

- `ProgramElimDeadWellFormed`;
- an address-parametric `ReachableExternalSpecCompatible` contract;
- hereditary active-code readiness at admissible entry states.

Thus the observable/runtime proof and program lifting are complete. The
remaining goal is to derive hereditary active-code readiness from the exact
compiler graph instead of accepting it as an entry premise.

### Hereditary preservation progress

The strong preservation layer retains exact compiler provenance after each
matched step. It is complete for:

- retained and deleted join declarations;
- cases, jumps, returns, and declaration entry;
- retained and deleted object, `USize`, and scalar writes;
- tag updates, increments, decrements, and deletion;
- retained and deleted erased lets;
- retained and deleted literal lets, including fresh-address extension for
  heap-backed literals;
- retained and deleted constructor lets, including fresh-address extension
  for paired live allocations and source-only unreachable garbage;
- retained and deleted object, `USize`, and packed-scalar projection lets;
- retained and deleted partial applications, including fresh-address
  extension for paired closures and source-only unreachable closure garbage;
- retained and deleted boxing, including tagged immediates and fresh-address
  extension for heap-backed boxes;
- retained and deleted unboxing, including publication of heap payload
  children as continuation roots;
- retained and deleted sharedness queries over related live ownership
  metadata;
- retained and deleted reset lets, with compiler-owned unreachable cells
  consumed only on the source side;
- retained and deleted reuse lets, including paired fresh allocation,
  in-place overwrite of related live cells, and source-only mutation of
  certified unreachable cells.

All stepping non-let code forms are therefore covered; `.unreach` is terminal.
All fourteen impure let-value families now have exact hereditary wrappers.
This includes retained and deleted `.fvar` applications, retained `.fap`
applications, and the deleted nullary-`.fap` boundary.

`ExactShadowCodeBinderReady.match_codeStep` assembles those family proofs into
one exact active-code dispatcher. The deleted nullary-`.fap` case is rejected
constructively: it cannot satisfy `DeletedLetReadyAt`'s generic
runtime-neutral equality because evaluating `.fap` produces an invocation,
not a value. Thus the local preservation proof does not assume this compiler
case is sound; compiler-facing entry readiness must exclude it or supply a
stronger constant-purity contract.

`SomeBinderReadyReachableMachineRelated.matchCodeStep_of_ready` now lifts the
exact dispatcher to complete machine states.
`binderReadyReachablyCodeReadyCompilerLaws` proves the resulting readiness
invariant stable across matched finite paths by path composition, and the
whole-program endpoint retains that strong invariant directly.

Canonical invocation entries and all non-code controls reconstruct strong
readiness without an active-edge premise. Hereditary yielded steps preserve
exact provenance through bind, apply, and cache frames; internal named calls
preserve it through cache hits, partial-application allocation, and internal
declaration entry. Closure calls and external waiting/resumption are covered
as well, so the exact machine dispatcher now spans every code and non-code
control reachable by the interpreter.

The checked whole-program endpoints expose the remaining semantic boundary in
three useful forms:

- exact runtime/ownership readiness for each future related pair;
- a hereditary source-only runtime/ownership invariant;
- a source-machine invariant for every selected entry, projected
  automatically into the non-lockstep relation.

`ElimDeadRuntimeAdmissibility` packages the first and third forms as the two
supported ways to discharge this boundary. `ElimDeadSemanticallyAdmissibleRun`
then combines one of those dynamic certificates with
`ProgramElimDeadWellFormed` and the successful transparent traversal.
`ElimDeadSemanticallyAdmissibleRun.loweringCorrect` is the corrected general
whole-program endpoint; address-parametric foreign compatibility remains a
separate, explicit consumer premise.

The client-facing ownership bridge is now inductive rather than
reachability-quantified. `ElimDeadSourceOwnershipContract` asks for an
entry-indexed one-machine predicate, its initial case, preservation by one
source step, and active-edge readiness. `ElimDeadExactOwnershipContract`
provides the corresponding source/target pair interface for ownership facts
that depend on the exact compiler residual and target heap shape. Generic
finite-path induction turns either contract into
`ElimDeadRuntimeAdmissibility`; `ElimDeadOwnershipContract` retains the
choice, and the checked correctness endpoint consumes it directly.

The neutral fixture instantiates the source-only interface. The deleted
owned-child reset/reuse fixture instantiates the exact pair interface:
separate finite source and target graphs preserve the contract, while the
target's empty frontier certifies that the concrete source reuse token names
an unreachable compiler-owned cell. These two fixtures check both branches
of the public bridge end to end.

Ownership-sensitive operations now have a reusable static-to-dynamic split.
`DeletedObjectSetLocalReadyAt`, `DeletedUSizeSetLocalReadyAt`, and
`DeletedScalarSetLocalReadyAt` record root-independent environment, heap-shape,
and slot-bound facts. `DeletedReuseSomeLocalReadyAt` does the same for a
concrete reuse token, while `DeletedResetLocalReadyAt` records a successful
reset outcome independently of its active roots. The write/reuse certificates
become dynamically ready when their source location is absent from the
address map; an empty related target frontier is a convenient sufficient
condition. For reset,
`ShadowRuntimeRel.leftRuntimeReachableFrame_of_rightNextLocation_zero` proves
that an outcome preserving the allocation frontier and non-heap observables
may rewrite any number of source-only garbage cells. The closed three-write,
one-cell reset/reuse, and owned-child reset/reuse fixtures now consume these
shared laws instead of rebuilding the mixed local/ownership existential at
each edge.

The empty-target shortcut is no longer the general ownership boundary.
`TargetAllocationLedger` records, for every address below the target
allocation frontier, the exact source allocation paired with it.
`SourceOnlyUnderTargetLedger` says that a source address is outside that
owner image. The runtime relation proves this criterion equivalent to
`rho.forward location = none`; empty ledgers initialize it, and paired fresh
allocations extend it while preserving older source-only locations. The
criterion now discharges all three write certificates and concrete-token
reuse. For reset, preserving the ledger-owned source cells yields the complete
reachable-runtime frame while leaving source-only cells unconstrained. A
kernel fixture with one retained paired allocation and one deleted
source-only allocation exercises the object-write bridge against a genuinely
non-empty target.

The ledger is now proof-relevant execution history rather than a certificate
reconstructed only at a final state. `LedgerShadowRuntimeRel` pairs the
ordinary runtime relation with its current `TargetAllocationLedger`.
`LedgerShadowRuntimeRel.empty` initializes both components,
`allocLeftGarbage` leaves the target ledger unchanged for a deleted
source-only allocation, and the proof-relevant `allocBoth` result extends the
ledger using the actual larger renaming returned by paired allocation.
`LedgerBinderReadyReachableMachineRelated` and its existential-renaming
wrapper expose this stronger history to machine clients, while their
`related` theorems forget it back to the established public relation. The
non-empty-target fixture now obtains its source-only write fact from this
carried history rather than constructing a final-state ledger by hand.

The literal-let family is the first exact non-lockstep matcher to consume and
return that history. `LedgerLiteralBothResult` distinguishes immediate
literals, which retain the current ledger, from heap-backed naturals and
strings, which extend it with their actual paired allocation.
`match_retainedLiteralLetStep_binderReady_ledger` carries that result through
the one-step target match; the deleted counterpart allows a source-only
literal allocation while the target stutters and keeps its ledger unchanged.
Exact traversal-view wrappers expose both branches at the compiler-facing
boundary. A retained large-Nat fixture forces the paired heap branch from
empty runtimes and proves that its post-state carries the enlarged ledger.

The constructor-let family now consumes the same history without collapsing
its two runtime representations. `LedgerCtorBothResult` records either the
unchanged renaming/ledger for an immediate nullary constructor or the actual
larger renaming and extended ledger for a heap-backed constructor.
`LedgerShadowRuntimeRel.publishEvalArgs` publishes covered constructor
arguments without changing allocation history, while
`allocCtorLeftGarbage` keeps the target ledger unchanged for a deleted
source-only constructor. Retained and deleted hereditary matchers carry those
results through non-lockstep steps, and exact traversal-view wrappers expose
both compiler branches. A one-field retained fixture forces paired heap
allocation through the exact wrapper; a nullary fixture proves definitionally
that the empty renaming, runtimes, frontier, and owner ledger are unchanged.

The partial-application family now carries the ledger through closure
allocation as well. `LedgerClosureBothResult` records the enlarged renaming,
related closure addresses, and extended owner ledger for a retained
underapplication; `LedgerPapLeftGarbageResult` records the source-only closure
and unchanged target history for a deleted underapplication. Hereditary
retained/deleted matchers and exact traversal-view wrappers expose both cases
at the compiler boundary. A retained fixture proves the paired closure
allocation from empty runtimes through the exact non-lockstep theorem, while a
deleted regression proves that the target ledger remains empty after the
source-only closure allocation.

The box family now carries the ledger through both of its runtime
representations. `LedgerBoxBothResult` distinguishes a tagged scalar or
`USize`, which preserves the current renaming and ledger, from a heap-backed
box, which returns the actual paired allocation and extended owner ledger.
The runtime proof first constructs this data-bearing result under `Nonempty`
and then selects it with `Classical.choice`, because eliminating the
proposition-valued value relation directly into data is not permitted.
`LedgerBoxLeftGarbageResult` records either the source tagged value or the
source-only heap allocation while preserving the target ledger. Hereditary
retained/deleted matchers and exact traversal-view wrappers expose both cases
at the compiler boundary. A retained large-`UInt64` fixture forces paired heap
allocation through the exact wrapper, and a deleted regression proves that
the target owner ledger remains empty after the source-only allocation.

The failed-token reuse family now carries the same history through its
constructor-allocation semantics. `LedgerReuseNoneBothResult` delegates to
the constructor primitive and therefore records either an unchanged ledger
for an immediate constructor or the actual paired heap-allocation extension.
`LedgerReuseNoneLeftGarbageResult` records the corresponding source-only
constructor result while preserving the target ledger. Specialized
hereditary retained/deleted matchers transport successful token and argument
reads through exact compiler provenance. A retained exact fixture forces
paired allocation from an empty failed token, while the deleted regression
proves that its source-only allocation leaves the empty target owner ledger
unchanged.

The concrete-token reuse branch now carries the ledger through its
existing-address semantics as well. Successful `setCell` and concrete
`reuse` operations preserve `nextLocation`, while
`TargetAllocationLedger.monoRenaming` transports the unchanged owner table
across the hidden renaming extension returned by the established runtime
simulation. `LedgerReuseSomeBothResult` packages the paired overwrite,
related result values, and transported ledger. Specialized hereditary and
exact retained matchers consume the token-reachability certificate; the
deleted matcher instead consumes a ledger-certified source-only location and
lets the target stutter. The retained exact regression starts from a genuinely
paired live constructor and overwrites it with a self-reference on both sides;
the deleted exact regression overwrites only an unmapped source cell while
the empty target ledger remains unchanged.

The first no-allocation layer now preserves the ledger uniformly.
`match_internalCoreSteps_binderReady_ledger` and
`match_sourceOnlyCoreStep_binderReady_ledger` lift the hereditary paired and
source-only determinism lemmas without changing the target allocation
history. Retained erased lets take their real step on both machines, while
deleted runtime-neutral lets take the source step and let the target stutter;
the generic exact wrapper covers erased values, copies, projections,
unboxing, and `isShared` whenever their local evaluation equation is
available. These branches no longer need operation-specific ledger proofs.

Retained full applications now preserve the ledger across their immediate
control-transfer step. `match_retainedFapLetStep_binderReady_ledger`
publishes the related evaluated arguments, pushes the exact paired bind
continuations, and enters matching named-invocation controls without changing
either runtime or the target frontier. Its exact wrapper consumes the audited
retained traversal view. A live nullary-call regression exercises the
observable boundary specifically: it retains the call, takes the paired
`.fap`-to-`invokeName` step, and carries the empty target ledger at frontier
zero. The later foreign response remains a separate allocation-capable
boundary rather than being hidden inside this theorem.

Join-point installation now carries the ledger through both compiler
decisions. A retained join takes one paired administrative step, installs the
related hereditary bodies in both join environments, and preserves the
target frontier. A deleted join installs only the unreachable source body and
is matched by target stuttering. The exact retained and deleted traversal
wrappers expose both rules directly to the future ledger dispatcher.

Retained returns now preserve the ledger while changing from active code to
yielded control. The proof transports the related live result values, narrows
the published roots to those values plus saved-frame roots, and takes one
paired return step. Since neither runtime changes, the exact target frontier
and owner history are carried unchanged. The exact return view exposes this
rule without retaining the consumed active graph.

Case selection now preserves the ledger through its complete successful
control path. The hereditary proof relates discriminator lookup, tag
extraction, and alternative choice, then takes one paired step into the
selected exact alternative. Faulting lookup/tag and missing-alternative
branches are terminal and cannot inhabit the semantic-step premise. Since
successful selection changes only control, the target frontier and owner
ledger are unchanged; the exact case view supplies the related alternative
table directly.

Retained local-value applications now carry the ledger through both immediate
semantics. The nullary `.fvar` branch binds the related function value into
both exact continuations; nonempty arguments publish the related function and
argument roots, push paired bind frames, and enter related `invokeValue`
controls. Neither branch changes either runtime. A dynamically certified
deleted `.fvar` is necessarily the runtime-neutral nullary copy, so the source
steps while the target stutters and retains the incoming ledger. Exact
retained/deleted wrappers expose the whole family to the future dispatcher.

Retained object-field projections now preserve the ledger as well. A generic
retained runtime-neutral let matcher separates the shared paired bind/control
step from each operation's local evaluation proof. The object specialization
transports a successful related field lookup, publishes the selected child as
a continuation root, and proves that the unchanged target runtime keeps the
same allocation frontier. Deleted object projections reuse the generic
source-step/target-stutter rule. Exact retained/deleted wrappers and a focused
compiler-view consumer exercise both interfaces.

Absolute-slot `USize` and packed-scalar projections now use the same ledger
path. Their retained matchers transport successful reads from related live
objects and bind equal immediate values, so neither heap reachability nor the
target allocation frontier changes. Their deleted exact branches stutter
through the common runtime-neutral rule. Together with object projection, all
three layout-field projection families now expose retained/deleted
ledger-aware exact wrappers.

Unboxing and ownership queries now complete the remaining read-only
object-consumer layer. The retained unbox matcher transports successful
unboxing across related live objects and publishes a heap-backed payload as a
continuation root when necessary; tagged payloads remain immediate. The
retained `isShared` matcher transports equal ownership metadata and binds the
related scalar result. Neither operation changes either runtime, so both
preserve the exact target frontier. Their deleted exact branches use the
generic runtime-neutral source-step/target-stutter rule. All four exact
retained/deleted wrappers are integrated at `3a12fe31`.

Internal named invocation now carries the ledger through its complete
`CoreResult.next` classification. Fully applied internal declarations enter
the exact related bodies while retaining the current target frontier; empty
cache hits publish an already-related global without changing either
runtime. Under-application allocates one paired closure and returns the actual
larger renaming and extended allocation ledger selected by that fresh pair.
`SomeLedgerBinderReadyReachableMachineRelated.matchInvokeNameNext` combines
the three outcomes and rules out unknown declarations, binding faults, and
external declarations for an assumed internal transition. This slice is
integrated at `dc4bea88`; external requests remain separate because their
responses may allocate.

The closed three-write chain also exercises the full client composition.
`closedWritesExactOwnershipContract` packages its separate source and target
finite graphs, one-step preservation, and exact-pair readiness as an
`ElimDeadExactOwnershipContract`. The fail-closed checker is proved to compute
the complete program target, and
`closedWritesCompilerAdmissibleRun` combines that equation, compiler
well-formedness, and the exact contract. Its public `LoweringCorrect` theorem
therefore uses the strict compiler-facing endpoint rather than the older
reachability-quantified helper.

The reset/reuse fixtures now use the same strict composition. The one-cell
fixture has been migrated from a bespoke hereditary invariant to
`closedConcreteReuseExactOwnershipContract`; it and the owned-child fixture
both expose checked whole-program equations and
`ElimDeadCompilerAdmissibleRun` packages. Their public `LoweringCorrect`
theorems therefore consume the conservative compiler policy together with the
exact finite-graph ownership proof, rather than stopping at the older semantic
admissibility endpoint.

The first compiler-facing policy is now explicit as well.
`NullarySafeShadowCodeRun` mirrors the transparent traversal while rejecting
exactly a deleted nullary `.fap`; retained nullary applications remain
admissible. `nullarySafeShadowCode?` is the corresponding fail-closed,
executable traversal. Successful checks reconstruct the proof-relevant graph,
and every graph computes the same checked result; the graph's mutual `result`
theorem then reconstructs the underlying `shadowCode?`/`shadowAltList?`
equations. Thus the executable policy cannot certify a different pass.
`nullarySafeShadowProgram?` lifts the checker through declarations and whole
programs, and `nullarySafeShadowProgram_certifies` derives both the exact
ordinary program result and `NoDeletedNullaryFapProgramRun` from one successful
checked equation.

`ElimDeadCompilerAdmissibleRun` combines that conservative pass policy with
the independently checked `ElimDeadRuntimeAdmissibility` package.
`ElimDeadCompilerAdmissibleRun.loweringCorrect` is therefore the strict
compiler-client endpoint under FIR's current impure semantics.
`nullarySafeShadowProgram_loweringCorrect` exposes the same result directly
from a successful checked-program equation, compiler well-formedness, the
runtime/ownership certificate, and foreign compatibility. The neutral
positive fixture reaches that endpoint end to end, while
`deadNullaryFapNotCompilerAdmissible` proves that the known effectful
counterexample cannot inhabit it. No suitable purity field was found in the
audited Lean 4.32 input to `elimDeadVars`; `Decl.safe` records termination
safety, not observational purity. A future semantics may replace this
conservative rejection with a stuttering certificate for selected constants.
An executable 11-row conformance matrix now checks Lean 4.32's pinned pass,
the transparent traversal, the fail-closed policy decision, and the exact
accepted target together. It covers neutral deletion, retained used and unsafe
bindings, deleted allocation/write/reset/reuse/PAP/box bindings, and both sides
of the nullary-application boundary. The pinned pass agrees on every row; the
only rejected policy row remains deletion of the effectful nullary
application. Kernel theorems pin representative retained-unsafe,
deleted-allocation, deleted-write, retained-nullary, and rejected-nullary
decisions. The accepted allocation row is also lifted through declarations and
programs into `ElimDeadCompilerAdmissibleRun`, then consumed by the strict
whole-program correctness endpoint.

Closed end-to-end fixtures now discharge those premises for deleted object and
scalar writes, failed-token reuse, concrete-token reuse, reset/reuse with an
owned child, partial-application closure allocation, and heap-backed scalar
boxing. Each fixture includes the finite source execution graph, concrete heap
shape or ownership facts, compiler well-formedness, a successful transparent
program run, and a public `LoweringCorrect` theorem. The PAP/box fixture also
pins the actual Lean 4.32 pass to the transparent target while proving that
both unreachable allocations may be omitted.

The remaining general problem is therefore not an operational matcher, a
missing whole-program theorem, an implicit nullary-purity assumption, an
unauditable policy graph, or a reachability-shaped client API. It is to
instantiate the inductive ownership contract for arbitrary compiler-produced
entry states from auditable static ownership facts: in particular, to carry
the target allocation ledger through arbitrary exact executions and derive
each local operation shape from compiler typing and ownership invariants. The
ledger now solves the address-map part without assuming an empty target, and
its proof-relevant carrier covers the allocation primitives and the complete
literal-, constructor-, partial-application-, box-, and failed-reuse-let
matchers, together with concrete-token existing-address reuse and the generic
runtime-neutral erased/deleted layer, plus retained/deleted local-value
applications, all three layout-field projection families, unboxing, and
ownership queries. It still has to be threaded through the remaining
closure/value invocation steps, existing-address mutations, and
allocation-capable external responses, then assembled into the unified
non-lockstep dispatcher and compiler-client invariant so arbitrary selected
edges receive that history rather than only focused fixtures.
`deadNullaryFapStaticPremisesButNotCorrect` proves in the kernel that
`ProgramElimDeadWellFormed` plus a successful transparent traversal cannot
imply correctness: the well-formed nullary-`.fap` counterexample has an
observable external effect under FIR's unrestricted foreign semantics.
Any stronger compiler-facing corollary must add such a semantic premise (or
exclude the disputed rule) and retain the explicit foreign-compatibility
contract.

### Open semantic boundaries

- `FIR-BUG-impure-elimDeadVars-nullary-fap-effects` is a real mismatch under
  FIR's current unrestricted external semantics: Lean treats a nullary full
  application as removable, while FIR permits it to emit observable effects.
  `deadNullaryFapStaticPremisesButNotCorrect` gives full static
  well-formedness, the successful transparent program run, and the negation of
  `LoweringCorrect` for one concrete external specification. Whole-pass
  correctness must therefore either exclude such programs, record the
  compiler's constant-purity invariant, or require a semantic stuttering
  certificate. The current `ElimDeadCompilerAdmissibleRun` endpoint chooses
  the conservative exclusion and has positive and negative kernel fixtures.
- `FIR-BUG-impure-none-external-spec-address-parametricity` is represented by
  the explicit `ReachableExternalSpecCompatible` premise. Arbitrary foreign
  semantics may inspect raw heap addresses and cannot be transported across a
  renaming.
- `FIR-BUG-impure-elimDeadVars-reuse-token-root-gap` is locally isolated by
  `RetainedLetReadyAt`, which requires a concrete reuse token's cell to be
  reachable. The compiler-facing proof must derive and preserve that
  capability.
- `FIR-BUG-impure-elimDeadVars-full-heap-observation` motivated the
  `ObservationRel`/`LoweringCorrect` endpoint. The active proof no longer
  compares raw heaps, although the shared unrestricted same-phase contract
  remains a separate cleanup target.

Actual-pass fixtures compare the transparent `elimDeadVars` shadow with Lean
4.32 and preserve every discovered mismatch as a textual bug card and
regression. The systematic policy matrix found no additional mismatch beyond
the existing nullary-`.fap` semantic discrepancy.

## Immediate proof queue

1. Preserve the ledger through closure/value invocation and the
   existing-address matcher families. Strengthen the foreign-response boundary
   when an external response allocates, then assemble the unified
   `SomeLedgerBinderReadyReachableMachineRelated` step dispatcher.
2. Define the ledger-aware entry-indexed exact ownership contract and use it
   to derive the ledger and source-only facts selected by arbitrary deleted
   write/reset/reuse edges, leaving only their local compiler
   typing/heap-shape certificates.
3. Extend the actual-pass matrix when new ownership laws or semantic
   boundaries produce a distinct compiler-relevant shape.
4. Adapt `scalarFromType_ok_eq_immediate` to the queued tagged-float runtime
   contract and prove the queued closure-application preservation consumers
   before that shared validation stack lands.

In parallel, the Wasm lane continues from the same final-impure semantic
boundary and runs constructor/projection artifacts through the shared
validation protocol.

## Trust and checked status

The Lean proof sources are fully elaborated without proof holes. The sole
registered project axiom is the pinned Lean 4.32 upstream-to-local
alpha-equivalence correspondence in `AlphaEqvTrusted`; `elimDeadVars` adds no
trusted axiom. `make check` validates the Lean build, executable examples,
differential matrices, bug-card format, source hashes, and the exact
trusted-axiom count.

Completing the immediate queue yields the first reachability-aware
whole-program proof for a behavior-changing final-impure pass. The remaining
reverse campaign then continues through projection movement, ownership,
late-mono lowering, SCC/lambda transformations, and finally the base/frontend
passes in the order above.

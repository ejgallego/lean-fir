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

All three local rewrite families now expose `CodeEquivalentAt` interfaces.
The singleton-default fixture eliminates directly; the unreachable-filter
fixture first proves the compiler-shape dead arm removable and then eliminates
the surviving singleton constructor; the alpha-fold fixture uses the
bidirectional checker theorem. Thus every actual-pass fixture has both an
executed syntax regression and a kernel-checked observational-equivalence
proof at its valid runtime tag. This deliberately separates local semantic
correctness from the still-missing compiler traversal graph.

Attempting to replace that command bridge with a kernel theorem exposed a
second upstream proof-interface gap. Lean 4.32 keeps `filterUnreachable`,
`addDefaultAlt`, `simplifyCases`, and recursive `Code.simpCase` module-private;
downstream code cannot even name the transparent first kernel, while the
recursive traversal is additionally an opaque `partial def`.
`FIR-BUG-impure-simpCase-private-proof-interface` records the failed minimal
statement and the required public graph/equation interface. FIR retains the
proved specification plus actual-pass regression without duplicating the
effectful compiler or adding another axiom.

The execution relation now also supports passes whose machines do not advance
in lockstep. `NonLockstep.Reaches` existentially hides a finite target step
count, and `StutteringSimulation` allows one source step to match zero or more
target steps while preserving a user-chosen relation between machine states.
Its soundness proof inducts over the source execution, and its composition law
transports the first pass's matching path through the second pass. Two such
simulations form a `StutteringBisimulation`, which proves equivalence of every
terminating observation without requiring equal programs or equal step counts.
`InitialStatesRelated` and `samePhaseCorrect_of_stuttering` isolate the remaining
pass obligation: relate the two programs' entry states.

`InternalPrefixOrEq` is the first genuinely non-lockstep regression. It relates
a state to itself or to the state after one deterministic internal step. In the
forward proof, that internal source step is matched by zero target steps; the
reverse proof replays it. The selected-arm case rewrite instantiates this
relation at a real `simpCase` boundary, proving the original case state and its
chosen branch observationally equivalent. The next proof slice should replace
this local one-step witness with a relation spanning the transformed program's
recursive traversal and declarations.

`NonLockstepExamples.ProgramStateRel` now supplies that first program-aware
slice. Its source and target contain different `main` declaration bodies: the
actual pass recursively traverses two `let`s and eliminates a closed singleton
case. The relation follows both machines from declaration invocation through
those continuations, permits the target to stutter at the eliminated case, and
rejoins them for return, nullary global caching, and extra-argument failure.
The resulting bisimulation relates every initial argument array and therefore
closes `SamePhaseCorrect` for the two distinct programs. An executable command
also confirms that Lean's actual 4.32 pass produces the proved target syntax.

The fixture constructs its discriminant internally. This is important:
singleton elimination is not observationally correct for every untyped raw
discriminant value, because the source inspects the value while the eliminated
target does not. Generalizing the program-aware relation to open case inputs
therefore requires the planned typed-entry/runtime invariant; it should not be
hidden by weakening the simulation or by silently restricting
`SamePhaseCorrect`.

`NonLockstep.Structural` now factors the fixture's reusable shape out of the
example. A caller supplies the relation on code bodies; FIR lifts it through
top-level declarations with identical ABIs, arbitrary-length ordered programs,
join declarations, saved bind continuations, control states, and finally the
whole machine. Pointwise program relatedness proves that every named lookup
returns related declarations, and it relates all initial machine states
without repeating entry plumbing. A concrete two-declaration regression pairs
the transformed `main` with an unchanged `helper` and checks both lookup and
arbitrary entry-state construction.

The same module introduces `SamePhaseCorrectOn`, `InitialInvariantOn`, and
`MachineRelatedWith`. Together they express the missing typed boundary without
changing the existing unrestricted correctness contract: admissible entry
arguments establish a relational machine invariant, the future non-lockstep
proof preserves it, and the generic lifting theorem returns correctness for
exactly those arguments. The next slice is to define the recursive
`simpCase` code relation and prove its core-step closure using this structural
machine relation.

The remaining bounded work is:

1. refactor FIR's opaque hygiene/binder traversals into transparent total
   definitions with equation lemmas, then derive `ProgramBodiesRelated` from
   `CheckedImpureProgram`/`ImpureHygienic`;
2. derive the two orientations of `CodeSideConditions`, environment coverage,
   and declaration-body coverage from the public checked-program boundary;
3. prove the transparent local checker sound for each newly added declarative
   code constructor, discharge or refine the exact runtime-type premises at
   the impure phase boundary, and eventually replace the audited upstream
   correspondence axiom with a kernel theorem;
4. once Lean exports a pass graph/equation interface, connect
   `filterUnreachable`, `addDefaultAlt`, `simplifyCases`, and recursive
   `Code.simpCase` directly to the local rewrite theorems;
5. lift the resulting theorem through declarations and program entry
   evaluation;
6. expand the compiler-generated conformance corpus around the whole pass;
7. in parallel, continue the Talos runtime work and run
   the constructor/projection examples end to end.

Completing those items finishes the first whole-pass theorem and the first
non-scalar Wasm differential test without forcing either track to wait for the
other.

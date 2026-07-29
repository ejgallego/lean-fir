# Optional Talos bridge

The detailed implementation, proof, and parallel-work plan is in
[`PLAN.md`](PLAN.md).

This package translates FIR's symbolic semantic-Wasm module into Talos's
`Wasm.Module`. It is intentionally separate from FIR's default build: Talos
is a fast-moving AGPL-3.0 project, while FIR's semantic core should not force
that dependency on every consumer.

The bridge is pinned to Talos commit
`a01d01c778b794dd00956748a067b6793c2c9f9b`, whose interpreter package uses
Lean 4.32.0. From the FIR repository root, set it up and validate it with:

```sh
make talos-setup
make talos-check
```

The adapter resolves FIR locals, symbolic branch labels, declaration calls,
runtime imports, function indices, and exports into Talos syntax. Host
implementations of the generated `fir.*` imports and the LCNF/Wasm simulation
proof live in this optional package rather than in FIR's core.

`FirTalos.runDifferential program entry args` runs the FIR interpreter and the
adapted Talos module together. It reports related observations, field-level
semantic mismatches, structured target failures, preparation failures, and
source fuel exhaustion while comparing only the observable reachable heap.

`FirTalos/Correctness/` now contains the W4 proof foundation: coherent handle
round trips, scalar codec lemmas, adapter signature/local/label/call
preservation, positional `HostEnv.Satisfies` packaging, and bridges from a
successful executable witness to fuel-free `TerminatesWith` and
`PartiallyMeets` observation statements. The first layer-4 slice additionally
proves natural/string literal lowering equations, relates their source and
semantic-host results, and lifts both operations through Talos's abstract
host-contract `wp` rule.

Constructor allocation, object projection, and tag lookup have the same local
source/host simulation relation. The handle invariant is preserved across
successful encodings, and out-of-range constructor tags are rejected before
the `Nat`-to-`i32` case comparison can truncate them. A common Talos `wp`
theorem lifts any exact successful semantic-host step through its abstract
host contract.

Generated constructor and object-projection call stacks now use that common
rule directly. The full adapted constructor test—from discriminator
`local.get` through `getTag`, `i32.eq`, and `if`—has a source-facing `wp` rule
that selects the same arm as the source `Nat` comparison. The proof found a
missing allocation-side tag bound; constructor allocations and alternatives
are now both rejected before an out-of-range tag can be narrowed to `i32`.

`FirTalos/Correctness/Composition.lean` adds the next W4 layer: generated
local-load prefixes, checked destination stores, complete constant/literal/
constructor/projection `let` sequences, and adapter equations for concatenated
instruction lists. `FirTalos/Correctness/Locals.lean` relates live source
environment bindings to compiler-resolved target slots, proves that checked
local writes preserve the frame, and keeps existing decoded values valid when
opaque-handle allocations extend the table. The executable `compileCode` now
uses a proof-transparent `partial_fixpoint` core instead of an opaque
`partial def`; successful `let`, `return`, and `unreach` equations feed a
`CodeAdapted` relation over the real compiler and adapter outputs. Successful
case equations now use the same executable compiler, and the structural
relations cover selected or generated fallbacks, skipped defaults, recursive
constructor alternatives, and their adapted Talos `if` programs.

`FirTalos/Correctness/Semantics.lean` begins the semantic induction with a
common related-state invariant, a `CodeWP` judgment over the actual compiler
and adapter witnesses, and a continuation-polymorphic direct-`let` rule. Its
first closed theorem covers a natural-literal `let; return` program from source
evaluation through handle encoding and checked local storage to a Talos return
whose result decodes to the exact source value. String literals now have the
same closed theorem, while constructor allocation and object projection use the
same recursive rule for arbitrary continuations. Semantic constructor cases
now use `CaseChainWP`: an adapted fallback seeds the chain, defaults are
skipped, and constructor hit/miss rules follow only the arm selected by the
source tag while retaining compiler evidence for both target arms. A complete
chain lifts directly to `CodeWP (.cases ...)`.
`FirTalos/Correctness/Function.lean` now supplies that store-specific bridge:
verified bodies yield `TerminatesWith` or `PartiallyMeets` under `RelatedPost`,
and exported wrappers preserve the concrete `findExport` resolution witness.
The adapter correctness layer now exposes its exact function/export layout,
and singleton `ReturnPost` proofs weaken to the observation postcondition used
by those wrappers. `FirTalos/Correctness/FunctionExamples.lean` closes the
first representative W3 instance: it follows the actual `abiLiteralProgram`
through lowering, adaptation, host resolution, local `CodeWP`, exported-name
resolution, and observation comparison to prove the premise-free
`abiLiteralMain_export_correct` total-correctness theorem.
`FirTalos/Correctness/FunctionCtorProjectionExample.lean` supplies the next
one: it composes the actual two-literal, pair-allocation, projection, and
return body and proves `abiCtorProjectionMain_export_correct`. This fixture
also generalizes the exported-return bridge to distinguish the initial source
runtime from the returned runtime, which is required once execution allocates
a heap object. `FirTalos/Correctness/FunctionCaseExample.lean` follows the
actual nested `Bool.false`/`Bool.true` tests and proves the premise-free
`abiCaseMain_export_correct`; its path-sensitive proof executes only the true
arm while retaining structural lowering evidence for the missed arm.
`FirTalos/Correctness/FunctionDefaultCaseExample.lean` completes the initial
four-program corpus: the false test misses into the separately compiled
default fallback and yields `abiDefaultCaseMain_export_correct`.
`FirTalos/Correctness/SupportedExport.lean` now factors the shared boundary:
one witness certifies fragment admission, lowering, adaptation, host
resolution, export/function lookup, and the single-result ABI, while its
common theorem turns the local `CodeWP` induction into total or partial
correctness for the named export. `FirTalos/Correctness/Program.lean` completes
W4's program-level induction for the certified call-free
literal/constructor/projection/case fragment. Its syntax-directed simulation
certificate derives the local `CodeWP`, a successful source evaluation, and a
real FIR `ExecEvaluates` run; `SupportedExport.execCorrect_of_simulation`
combines that run with fuel-free correctness of the generated named export.
All four fixtures use this API without fixture-specific `CodeWP` recursion.
W5.1–W5.8 now cover scalar/`usize` projections, boxing and sharing, mutation,
ownership, reset/reuse, semantic external calls, and source-compatible lazy
global caching. Called zero-argument declarations use deterministic mutable
flag/value globals; misses update both the semantic runtime and physical Wasm
cache, while hits skip evaluation. Differential coverage checks that two calls
produce one external event, and the proof surface covers exact cache host
steps, the compiler/adapter cache shape, zero-argument declaration-body
packages, hit/miss WP composition, miss-publication-to-hit facts, recursive
`CodeWP`, and the checked-export boundary. The first concrete body family
composes witness-growing natural and UTF-8 string literals with the generated
return suffix across `.tobject` and `.object` result lanes; constructor
allocation bodies retain either tagged or heap-backed refinement through that
same suffix. Internal direct and recursive calls now use ordinary Wasm calls.
Statically tracked closures use a generated metadata trampoline with typed
capture projection, semantic underapplication, and saturated direct dispatch;
the supported gate rejects oversaturation and unknown closure provenance.
Differential coverage includes direct, captured, underapplied, and recursive
programs, completing the planned W5 semantic-backend slices.

W6 now has a frozen `wasm32-lean64` concrete data model. Object addresses and
lanes are `i32`, source `USize` remains `i64`, constructor/capture slots are
eight bytes, and large semantic tagged values are promoted to persistent heap
naturals by the refinement relation. The first concrete runtime slice provides
checked little-endian linear memory, page growth, aligned allocation, and a
self-describing live/dead object header. Immediate and promoted tags, empty
and allocated constructors, checked object/`USize` projection, and arbitrary
natural limbs now execute over that memory. The semantic Talos host remains
the oracle while concrete heap-state and operation refinements are proved one
vertical slice at a time.

W6 compiler correctness now has a certificate-free public track.
`ConcreteSupportedExport` statically ties the selected LCNF code to the actual
`compileCode` and Talos-adapter body and records the compiler's local-layout
alignment plus the adapter/resolver's runtime-call contracts.
`ConcreteSupportedExport.correctReturn` is the first direct case:
given a source return evaluation and an initially related concrete state, it
derives the generated numeric return body and matching exported Talos
execution. `correctNaturalLiteralReturn` adds the first compositional
`let; return` case: the exact generated call/local-write/read/return body,
concrete allocation, witness extension, and resolved host contract are joined
without a caller-supplied simulation certificate.
The same module now inverts any successful direct-`let` compilation into its
separately compiled/adapted value and continuation. Its natural-literal
specialization composes allocation and the generated destination write with
an arbitrary continuation correctness hypothesis selected by the compiler,
which is the recursive rule needed by the structural proof.
The UTF-8 String specialization mirrors that boundary in the `.object` lane,
including a finite exported `String; return` theorem derived from the real
compiler, adapter, concrete resolver, allocator, and return suffix.
The constructor specialization now covers the complete current `compileArg`
language: ordinary `fvar` fields become compiler-resolved numeric local reads,
while erased fields become canonical `i32.const 0` operands.
`ConstructorArgsCompiled` characterizes the production `compileArgs` fold,
and source evaluation plus `StateRelated` derives the exact physical operand
prefix without a caller-supplied readiness witness. `codeWP_constructorLet`
composes an arbitrary continuation, and `correctConstructorReturn` closes the
finite export. The earlier all-`fvar` theorems remain compatibility
specializations.
Object, `USize`, and packed integer projections now share one generic
`localRuntimeCallLet_eq` inversion. Their public recursive rules derive the
numeric object/result locals, runtime import, concrete resolver contract, and
physical object operand from the real pipeline and `StateRelated`, then
compose the existing W6 heap refinements with any verified continuation.
Successful object and `USize` source reads now recover the constructor
descriptor directly from `ConcreteRuntimeRel`; clients no longer restate
descriptor existence. Object projection retains only selected-field ABI-kind
agreement, and `USize` projection has no remaining heap-shape premise.
`DirectValueEvaluates` and `codeWP_of_directValueEvaluates` now assemble these
one-node boundaries into the first real structural theorem: arbitrary finite
return/direct-value spines are proved by induction while the target split and
numeric destination at every node are recovered from the production compiler
and adapter. The exact remaining condition is
`DirectLetRuntimeRefines`: every admitted successful direct source step must
have a matching concrete step that establishes the related continuation state
and preserves the selected resource invariant. This is a uniform runtime law,
not a caller-built source/target derivation.
The first such law is now constructive for zero-argument local aliases.
`ConcreteLocalFrameAligned` records exact target-frame capacity independently
of `StateRelated`; compiler-resolved local lookup proves each write is
in-bounds, and the checked write preserves that invariant. A two-alias contract
harness obtains both generated read/write pairs and every numeric slot from
the real compiler and adapter.
The same law is now constructive for read-only `USize` projections:
`USizeProjectionSupported` contains source/compiler typing facts only, while
the real adapter, related local frame, concrete heap relation, and resolved
host recover the numeric read/call/write prefix and its successful concrete
step. Object projections now use the same boundary, with selected-field
ABI-kind agreement represented as their one source typing obligation.
Packed integer projections join it through `ScalarValueKind`, the
target-independent source typing relation between `UInt8/16/32/64` semantic
constructors and their ABI lanes. `scalarProjStep_of_refines` derives the
matching concrete read and physical value for every successful source read.
`DirectLetRuntimeRefines.or` and `ReadOnlyDirectSupported` compose local
aliases, nonallocating `UInt8/16/32/64` and `USize` literals, plus all three
projection families into arbitrary mixed spines. Literal classification
derives the symbolic constant, adapted Talos instruction, physical value, and
semantic value without a target witness. The structural contract harness
accepts the combined fragment without a descriptor, concrete read, numeric
layout, or translation-certificate premise. This success theorem does not
weaken the recorded uninitialized-coordinate fault discrepancy:
`FIR-BUG-wasm-none-uninitialized-scalar-projection` remains the boundary for
full structured-fault correspondence.
Allocating proofs now use an explicit, compositional wasm32 resource boundary
instead of opaque success assumptions. `MemoryState.AddressSpaceBudget`
measures aligned remaining address space and has an exact consumption law;
`AllocationCapacity` specializes it to one request. Raw allocation, object
allocation, and complete UTF-8 String allocation are constructive from this
headroom plus the alignment already present in `StateRelated`.
`codeWP_stringLiteralLet` and `correctStringLiteralReturn` therefore assume
only String allocation capacity and derive `allocateString = .ok ...`
internally. The boundary is deliberately unstable while the structural
source-path budget is developed; clients should expect to adapt as
constructor and heap-Nat cases join it. Nonempty constructor allocation now
also constructs its heap/address result from exact `ConstructorLayout`
capacity at both the memory and concrete-operation refinement boundaries; the
compiler theorem derives argument decoding and pointwise field refinement
from compilation, evaluation, and `StateRelated`, so its public recursive and
finite APIs no longer accept a concrete constructor-step witness. Sequential
allocation now has its first recursive transport rule:
`codeWP_stringLiteralLet_of_budget` gives an arbitrary generated continuation
the exact residual source-path budget after UTF-8 allocation. Object and
constructor allocation expose the same exact residual boundary below the
compiler. `codeWP_of_directValueEvaluates_withCost` and
`DirectLetRuntimeRefinesWithCost` now provide the before/after indexed
structural law, and the String instance proves arbitrary finite String-literal
spines from one source-computed budget. The nonempty-constructor instance now
does the same for arbitrary constructor spines, deriving mixed local/erased
physical arguments and every concrete allocation internally.
`BudgetedDirectSupported` now permits arbitrary interleavings of these two
allocating families with cost-zero local aliases and immediate integer/`USize`
literals plus successful object, `USize`, and packed-integer scalar
projections under one source path budget. The projection laws expose exact
heap preservation across their generated readers, so the complete residual
budget reaches the continuation.
Natural literals now join the same indexed fragment across their three
wasm32 representations. `naturalAllocationBytes` assigns zero bytes to
immediates, an aligned one-slot object to promoted source tags, and the exact
aligned limb-object extent to arbitrary-precision heap naturals.
`allocateNatural_eq_ok_of_budget` constructs the selected representation and
returns the exact unused headroom, allowing arbitrary Nat-literal spines and
mixed direct spines to use the same single source-computed budget. This
proof-facing cost surface is intentionally allowed to evolve with the
implementation.
`ConcreteSupportedExport.correctBudgetedDirect` packages that structural
result at the named-export boundary: successful finite source evaluation and
one initial budget imply the matching executable source observation and
fuel-free concrete Wasm termination under `RefinedReturnPost`, with no
translation certificate or target-level witnesses.
The next structural layer covers external calls without inventing an `Int`
literal that Lean 4.32 LCNF does not have. `BudgetedSpineEvaluates` mixes
direct lets with each exact three-step source external protocol and indexes
the path by its required allocation budget. Direct costs remain
syntax-computed; external result costs are source-execution indices because
arbitrary-precision result size can depend on the response.
`ExternalLetRuntimeRefinesWithCost`,
`codeWP_of_budgetedSpineEvaluates`, and
`ConcreteSupportedExport.correctBudgetedSpine` then compose reusable external
operation-family theorems with the production compiler/adapter and preserve
the source's exact trace. `integerAllocationBytes` and
`allocateInteger_eq_ok_of_budget` construct the current heap-`Int`
representation from one source-facing budget. The reusable
`ConcreteExternalImpl.IntegerResultRefines` law and its budgeted invocation and
Talos-step theorems now add the exact response, witness extension, related
runtime/value, and unused headroom without caller-supplied allocation or
target witnesses. `PureIntegerExternalSupported` admits compiler-shaped
`Int.ofNat` and `Int.neg`, and
`externalLetRuntimeRefinesWithCost_pureInteger` reconstructs their argument
prefix, external import, host contract, allocation, local write, exact source
trace, and residual budget from production compilation and static resolver
alignment. Costed direct runtime laws now also prove that they preserve the
installed concrete external implementation. The generic lift
`preservingExternalInvariant` carries the integer-handler family law through
all current direct operations, and
`correctBudgetedIntegerExternalSpine` proves a named export correct for
arbitrary finite interleavings of those direct operations with
`Int.ofNat`/`Int.neg`. Its caller supplies only source evaluation, the initial
state/frame relation, one exact path budget, and the initially installed
handler law. This proof-facing surface is intentionally unstable.
`ConcreteCompilerCorrectnessContract.lean` keeps the finite export
applications and the literal/constructor/projection recursive APIs on the
certificate-free boundary, including the new structural theorem, under
`make talos-check`.
Existing certificate-shaped modules are retained only as internal sources of
operation and invariant lemmas while projection/allocation instances of the
concrete direct-runtime law, control-flow, calls, externals, caches, and faults
are migrated. The first
endpoint preserves finite source behaviors conditionally;
later finite-trace and weak-simulation work will cover divergence without
proving source termination.

The plan also defines A0, an independent artifact lane that can run alongside
the proof and concrete-runtime lanes. A0 owns emitter and external-engine
runner paths and produces standards-consumable, host-backed Wasm artifacts for
the W3--W5 semantic corpus. It consumes the frozen semantic ABI unchanged;
concrete linear-memory layout and production ABI compatibility remain W6 work.

The A0 corpus compares successful returns, entry arguments, reachable heaps,
world/trace effects, and structured runtime faults against live FIR
observations. Semantic host
faults use the same constructor-and-fields JSON shape as the Lean oracle;
runner assertions and target-integrity failures remain fatal harness errors.
Compiler-produced source artifacts may also carry an `initialRuntime` manifest
object. The V8 host reconstructs its FIR heap before turning semantic object
arguments into opaque `i32` handles; this covers a real string input, and W5
ownership operations are available to compiler-produced programs as semantic
imports as well.
Structured source invocation also covers `List Nat` constructor graphs. The
fixture includes a natural beyond the tagged-immediate range, checks the full
reconstructed list, and executes a compiler-produced constructor case through
the semantic `getTag` import in V8.
The artifact and validation runners import the same semantic host module. The
main native↔V8 validation matrix now exercises that constructor graph directly
from the shared corpus and receipts the host as a captured runtime tool.
It also checks Lean 4.32's scalar `UInt8` result representation for `Bool`,
accepting only zero and one at both the LCNF and V8 schema boundaries.
`#fir_wasm_emit_case "case-id"` consumes the validation corpus directly. Its
schema-driven API checks argument datums and the emitted result lane, carries
case dependencies into capture, and preserves the case ID in the artifact
manifest.

The W5 adaptation is complete for the semantic-backend contract. Manifest
serialization and the shared Node host cover every W5 operation emitted by the
supported backend, including cache set, externals, closure construction and
metadata, and generated direct, recursive, saturated, and underapplied calls.
The older `closureApply` host callback remains rejected deliberately: W5 uses
generated metadata trampolines and direct dispatch instead. Join-point-bearing
source declarations and additional initial-runtime heap-object encodings are
corpus/adapter expansion work, not missing W5 runtime operations. The default
native--V8 matrix contains 39 compiler-produced cases, while the independent
Talos--V8 artifact lane compares 34 fixtures. Large odd `Nat` values are kept
out of the JSON adapter until `FIR-BUG-wasm-none-json-nat-precision` is fixed.
The scalar-case admission slice additionally passes seven targeted
native--V8 cases—both Boolean branches, a three-way nullary enum, and four
signed-`Int` boundaries—bringing the ready generation set to 46 once the
root-owned default-matrix list is updated.

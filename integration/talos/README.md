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
composes a witness-growing natural literal with the generated return suffix.
Internal direct and recursive calls now use ordinary Wasm calls.
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

# FIR WebAssembly and Talos plan

This document is the source of truth for the WebAssembly track on branch
`wasm/talos-runtime`. Work takes place in `.worktrees/wasm-talos` under the
parallel-development rules in `AGENTS.md`.

The track owns `Fir/Wasm/`, `integration/talos/`, and Wasm-specific bug cards.
Changes to the semantic Wasm ABI are shared-contract changes: isolate them in
their own commit, describe their effect on both tracks, and coordinate landing
them through the integration owner before dependent work continues.

## Goal

Relate executions of final impure LCNF to executions of generated WebAssembly
in Talos. The first target is a semantic backend with an abstract host runtime;
a later refinement will replace that host model with a concrete linear-memory
runtime.

```text
final impure LCNF
        |
        | Fir.Wasm.lower
        v
FIR symbolic Wasm -- static checker --> Talos Wasm.Module
                                              |
                         +--------------------+--------------------+
                         |                                         |
                  semantic host runtime                later linear-memory runtime
                         |                                         |
                         +------------ refinement proof -----------+
```

This layering separates three claims:

1. LCNF is lowered to the intended Wasm control and data flow.
2. Runtime imports implement their abstract FIR operations.
3. A concrete memory layout refines the abstract runtime.

The first proof should establish claims 1 and 2 without prematurely fixing a
production heap layout.

## Current status

- W0 is complete: the semantic ABI, checked kinds, stable imports, opaque
  handles, target failures, and supported-fragment guards are in place.
- W1 is complete: FIR validates the generated symbolic subset before
  adaptation, Talos validation is an additional guard, and function origins
  survive conversion.
- W2 is complete for natural/string literals, constructor allocation, object
  projection, and constructor tags. The positional host resolver, typed codec,
  structured source/target traps, abstract contracts, and executable Talos
  guards live under `integration/talos/FirTalos/`.
- W3 is complete: `runDifferential` runs both semantics, encodes entry
  arguments, classifies all Talos outcomes, and compares outcome, world,
  trace, and the canonical reachable heap. Its result carries field-level
  mismatch evidence.
- W4 proof infrastructure is in place: coherent handle-codec round trips,
  scalar lane lemmas, adapter signature/local/label/call preservation,
  positional host satisfaction, and fuel-free observation postconditions.
  The adapter recursion is now terminating and transparent to proofs.
- W4 layer 4 now has local lowering and source/host simulations for natural
  and string literals, constructor allocation, object projection, and tag
  lookup. Successful handle encodings preserve a chainable coherence/freshness
  invariant, and checked `UInt32` tag bounds make case comparisons injective.
  Exact successful host steps have a common instruction-level Talos `wp`
  lifting through abstract host contracts, with specialized literal rules.
  Target handle-space availability is an explicit premise rather than an
  implicit infinity assumption.
- Generated constructor and projection call stacks now instantiate that common
  `wp` rule. The complete adapted `local.get; getTag; const; i32.eq; if`
  sequence selects the same constructor arm as the source `Nat` comparison,
  including restoration of the operand tail across both arms. Completing that
  proof exposed and fixed the missing allocation-side constructor-tag bound;
  both allocated and compared tags are now checked before narrowing to `i32`.
- W4 straight-line composition now covers checked `local.get` sequences and
  `local.set`, i32/i64 constant lets, natural/string literal lets, constructor
  lets with local fields, and object-projection lets. Adapter proofs distribute
  instruction conversion over concatenation and join independently adapted
  value/continuation sequences at the resolved numeric destination local.
- W4 now has the source-environment/target-local relation used to chain those
  rules. It is stated through the adapter's own `findFVar?` resolver, is stable
  under handle-table extension, and is preserved by checked destination writes.
  Successful opaque-handle encoding supplies both the table-extension proof
  and the decoded destination value, so existing aliases remain valid after a
  constructor, projection, or literal result is bound.
- The executable lowerer's recursion is now proof-transparent without a
  duplicate compiler. `compileCode` is a stable `Except` wrapper around an
  `ExceptT CompileError Option` `partial_fixpoint` core, whose generated
  equation exposes one structural layer while retaining the same runtime
  implementation. Successful equations are proved for `let`, `return`,
  `unreach`, and `cases`. `CodeAdapted` composes the actual symbolic compiler
  output with the numeric Talos adapter. Its case layer now represents default
  selection, the generated unreachable fallback, skipped defaults, recursive
  constructor alternatives, and the final Talos `if` explicitly through
  `CaseFallbackAdapted`, `CaseChainAdapted`, and `CasesAdapted`.
- W4 semantic composition is factored in
  `FirTalos/Correctness/Semantics.lean`. `StateRelated` joins the retained
  source runtime, clear target-failure channels, the handle invariant, and
  compiler-resolved related locals. `CodeWP` combines that invariant with the
  real compiler/adapter witness and Talos total-correctness `wp`.
  `LetStepSimulates` is the reusable recursive boundary for direct `let`
  operations. Closed theorems prove complete natural- and string-literal
  `let; return` chains, including source evaluation, handle encoding, checked
  local binding, target return, and decoding of the exact source result.
  Constructor allocation and object projection now instantiate the same
  recursive boundary, including multi-local argument loading, source heap
  operations, handle-table extension, and continuation composition.
- W4 semantic cases now thread the common state invariant and arbitrary
  postcondition through the actual fallback/constructor chain. `CaseChainWP`
  has rules for an adapted fallback, skipped defaults, constructor hits, and
  constructor misses. The hit rule requires semantic correctness only for the
  selected source arm; the miss rule recurses only through the selected suffix,
  while both retain structural compiler evidence for the unexecuted arm. The
  complete chain lifts to `CodeWP (.cases ...)` through the executable case
  compiler.
- The local W4 judgment now reaches Talos's public fuel-free execution
  predicates. `FunctionBodyPost` installs the verified body at one concrete
  runtime/handle store, `CodeWP.toTerminatesWithRelated` and its partial
  counterpart produce `RelatedPost`, and exported-name wrappers retain the
  module's actual `findExport` witness. This store-specific bridge avoids the
  stronger store-polymorphic premise required by `FuncSpec`.
- Whole-module adaptation now exposes an exact layout theorem for the mapped
  imports, pointwise-adapted functions, and unified-index exports. Singleton
  result decoding feeds directly into target observations, and a closed
  `ReturnPost` can be weakened to `RelatedPost` and lifted to total correctness
  for a resolved single-result export.
- `FirTalos/Correctness/FunctionExamples.lean` instantiates that stack on W3's
  real `abiLiteralProgram`. It extracts the checked symbolic module, adapted
  Talos module, resolved host environment, exported `main`, and concrete
  initial store; proves the local natural-literal `CodeWP`; and packages it as
  the premise-free `abiLiteralMain_export_correct` total-correctness theorem.
  The conclusion uses the same `compareObservations` policy as the executable
  differential harness, rather than a proof-only observation relation.
- `FirTalos/Correctness/FunctionCtorProjectionExample.lean` now closes the
  second W3 fixture. It composes two literal calls, a pair allocation, object
  projection, four checked local writes, and the generated return across the
  exact 13-instruction adapted body. The export bridge separately tracks the
  initial and returned source runtimes, so the premise-free theorem retains
  the constructor heap created during execution instead of assuming the
  source runtime is unchanged.
- `FirTalos/Correctness/FunctionCaseExample.lean` now closes the explicit
  constructor-case fixture. It follows the generated nested tag tests: the
  `Bool.false` arm is structurally adapted and missed, the `Bool.true` arm is
  selected, and only that arm receives the path-sensitive semantic proof.
  The final `abiCaseMain_export_correct` theorem covers the real four-import,
  two-local adapted export without runner fuel or unselected-arm execution.
- `FirTalos/Correctness/FunctionDefaultCaseExample.lean` closes the fourth W3
  fixture. The compiler-selected default is adapted once as the symbolic
  fallback; the generated `Bool.false` test misses and resumes that fallback,
  producing the premise-free `abiDefaultCaseMain_export_correct` theorem.

All four representative exports are now closed, and W4 is complete for the
certified call-free literal/constructor/projection/case fragment.
`FirTalos/Correctness/SupportedExport.lean` factors their repeated
whole-pipeline packaging into one reusable witness and theorem, independently
of fixture-specific checked layouts. A witness records `WasmSupported`, the
actual `lowerSupported` result, source-function lookup, adaptation, resolved
hosts, export/function lookup, and the single-result ABI. Given the local
semantic certificate and an observation-policy fact, the common theorem yields
both FIR `ExecEvaluates` and Talos `ExportTerminatesWith`; partial correctness
is an immediate corollary. `FirTalos/Correctness/Program.lean` supplies the
syntax-directed `CodeSimulation` induction, its `CodeWP` corollary, successful
source evaluation, and the proof that this evaluation executes in the shared
FIR interpreter. All four fixtures instantiate this API without their former
fixture-specific `CodeWP` recursion. Target resource availability remains an
explicit simulation premise because the finite opaque-handle table can be
exhausted. The adapter still rejects initializers and closures; those are W5
extensions rather than gaps in the initial theorem domain.

An independent artifact lane, A0, may proceed in parallel with W4. It turns
the already checked semantic module into a standards-consumable host-backed
Wasm artifact and runs the W3 corpus in an external engine. A0 does not define
the production linear-memory ABI and must consume, rather than modify, the
frozen semantic ABI and supported-fragment boundary.
It now emits closed and parameterized compiler-produced scalar sources and
heap-backed source invocations with an explicit initial FIR runtime. The
Node/V8 host reconstructs that heap before assigning opaque Wasm handles.

## Cross-lane coordination board

| Date | Producer | Consumer | Status | Item |
|---|---|---|---|---|
| 2026-07-17 | A0 source emission | W4 ABI/validation proofs | resolved | `FIR-BUG-wasm-none-compiler-nat-literal-kind` is fixed: the compiler invariant admits `tagged` or `tobject` natural literals, a theorem proves invariant acceptance implies lowering acceptance, and the captured Lean 4.32 `litNat` module emits reproducibly and returns `42` in Node/V8. The separate hand-built `object` compatibility exception was not folded into the compiler invariant. |
| 2026-07-17 | A0 source emission | W4 and integration owners | landed | `4841a09` adds `#fir_wasm_emit`, which captures an actual Lean 4.32 final-impure declaration and deterministically emits `.wasm`, `.wasm.json`, and `.wasm.lcnf`. The original smoke test used a closed `UInt64` declaration; W4's invariant repair now also emits and executes the compiler-produced `Nat` declaration without normalizing its captured LCNF. |
| 2026-07-17 | A0 parameterized source emission | W4 and integration owners | landed | Source capture/lowering now produces a reusable module artifact before a checked semantic invocation is attached. `#fir_wasm_emit` accepts range-checked integer and tagged argument syntax; the compiler-produced `idUSize : USize → USize` fixture carries its `usize` schema and argument through the manifest and returns `42` in V8. No shared ABI or supported-fragment contract changed. |
| 2026-07-17 | A0 scalar source arguments | W4 and integration owners | ready | Compiler-produced identity declarations for `UInt8`, `UInt16`, `UInt32`, and `UInt64` now execute at maximum-width inputs in V8. Arguments come from the checked manifest, and target `i32` results are normalized to their declared unsigned source widths. No shared contract changed. |
| 2026-07-17 | A0 heap-backed source arguments | W4 and integration owners | ready | Source manifests can now carry a checked `initialRuntime` heap, and `#fir_wasm_emit` accepts string literals by allocating them in that runtime. V8 reconstructs the heap and passes an opaque handle to a compiler-produced `String → UInt64` fixture. The full `idString : String → String` capture is intentionally deferred: Lean 4.32 emits `inc[ref] value; return value`, and ownership operations remain in the W4-owned supported-fragment lane. No shared contract changed. |
| 2026-07-17 | A0 structured source arguments | W4 and integration owners | ready | `#fir_wasm_emit` now accepts `natList([...])` and builds the corresponding FIR constructor graph, including heap naturals beyond the tagged-immediate range. A compiler-produced `List Nat → UInt64` fixture executes `cases` through the imported `getTag` host operation in V8 and distinguishes the nonempty constructor. The test reconstructs and checks the entire input list before invocation. No shared contract changed. |
| 2026-07-17 | A0 schema-driven source invocation | validation and integration owners | ready | `compileValidationInvocation` encodes corpus schemas/datums, checks the declared result schema against the emitted ABI lane, and chooses the scalar or initial-runtime manifest path. `#fir_wasm_emit_case "…"` resolves entry, dependencies, arguments, and schemas from one corpus case. The five scalar source fixtures and `FirValidationWasm` now share this boundary. No shared semantic contract changed. |
| 2026-07-17 | A0 shared semantic host | validation and integration owners | landed | The artifact and validation V8 runners now share one manifest/runtime/handle/import implementation. The native↔V8 matrix admits `nat-list-nonempty`, audits its entire initial heap against the corpus schema, and executes the compiler-produced `getTag` import. The additive common corpus case landed separately as `09d3c06`; no semantic ABI changed. |
| 2026-07-17 | A0 scalar Boolean results | validation and integration owners | landed | `nat-list-nonempty-bool` exposed `FIR-BUG-impure-none-bool-result-scalar`: Lean 4.32 returns `Bool` as scalar `UInt8`, while validation accepted only tagged objects. Shared commit `f9cdeb2` admits exactly scalar zero/one in LCNF observations; the Wasm schema and V8 decoder now mirror that boundary. The native↔LCNF and native↔V8 matrices retain the case as a regression. |

Shared-contract changes in these A0 slices are the additive common
`nat-list-nonempty` case in `09d3c06` and the scalar-Boolean observation
boundary plus regression case in `f9cdeb2`. The runtime step semantics and
`AbiKind` vocabulary are unchanged. W4 has repaired and proved the
natural-literal invariant; A0's former rejection regression is now a successful
source-to-engine test and the bug card is fixed.
A0 has now separated module generation from fixture invocation and covers all
unsigned integer and `USize` parameter kinds with explicit ABI schemas. Its
initial-runtime manifest uses the same value, heap-cell, and heap-object JSON
vocabulary as the W3 observation oracle. Its next heap-returning source slice
depends on W4 admitting and proving the compiler-produced ownership operation;
the shared semantic host and the first initial-runtime validation case are now
landed. Independent A0 work can next broaden schema-directed results whose
compiler-produced LCNF is already inside the proved supported fragment.

## Architecture decisions

### Two-level type information

Do not use a physical Wasm type as the only description of an LCNF value.
Several semantically different values share the same stack representation.
Introduce an ABI kind along these lines:

```lean
inductive AbiKind
  | object | tagged | tobject
  | erased | reuseToken
  | uint8 | uint16 | uint32 | uint64 | usize
  | float32 | float
```

The physical representation is derived afterward:

| ABI kind | Semantic Wasm representation |
|---|---|
| object, tagged, tobject, erased, reuse token | `i32` handle or sentinel |
| `UInt8`, `UInt16`, `UInt32` | `i32` |
| `UInt64`, semantic `USize` | `i64` |
| `Float32` | `f32` |
| `Float` | `f64` |
| void | no stack value |

Keeping semantic `USize` as `i64` matches FIR's current abstract runtime. This
is the semantic ABI, not yet a claim about a production wasm32 pointer ABI.
A later target-specific refinement can map `USize` to wasm32 `i32` with the
appropriate source-side word-size semantics.

Function parameters, locals, results, runtime operations, and imports must
retain `AbiKind`. Physical Talos signatures are projections of that metadata.
Unknown impure types must be rejected instead of silently defaulting to `i32`.

### Opaque handles

Use `i32` as an opaque handle into host-managed values, rather than encoding
FIR heap locations or tagged payloads directly. A first host state should be:

```lean
structure RuntimeHost where
  runtime : Fir.LeanIR.Impure.RuntimeState
  handles : HandleTable
  fault? : Option Fir.LeanIR.Impure.RuntimeFault
```

The handle table should reserve a sentinel, intern equal object-like values,
preserve aliases, allocate deterministically, and report exhaustion as a
target resource failure. Host operations decode handles, reuse the FIR runtime
operations, and encode results back to Wasm values.

Keeping the structured fault in host state allows a Talos trap to be related
to `RuntimeFault` without making theorem statements depend on trap strings.

### Closures are a separate gate

Talos host functions cannot call back into a Wasm-defined function. Therefore
the current `closureApply` import cannot be the final implementation of LCNF
closures: delegating it to the FIR interpreter would make the backend theorem
circular.

The first correctness fragment excludes `pap` and closure-valued `fvar`
applications. Before enabling them, choose and document one real dispatch
design:

- a function table plus `call_indirect` and typed wrappers;
- a uniform boxed calling convention and dispatcher; or
- a Wasm-level trampoline protocol.

The choice must specify heterogeneous captured values, oversaturated calls,
recursive targets, and the representation of fixed arguments.

### Initializers are explicit work

`Fir.Wasm.Module.initializers` is currently ignored by the Talos adapter. Do
not silently map every zero-parameter declaration to a Talos start function.
First decide whether the semantic backend uses:

- explicit initialization invoked by the harness;
- a generated aggregate start function; or
- source-compatible lazy global evaluation.

Until then, the proved fragment excludes programs whose behavior depends on
global initialization or lazy caching.

### Validation belongs to FIR

Talos's current `Module.validate` is deliberately partial and accepts control
flow or instructions its stack checker does not model. Add a complete checker
for FIR's generated symbolic subset. It must cover:

- unique parameters, locals, join labels, declarations, and exports;
- local and label resolution;
- operand-stack ABI kinds through every symbolic instruction;
- call arguments and results;
- block, branch, case, and return stack shapes;
- import ordering and runtime-operation signatures; and
- initializer and entrypoint restrictions for the current fragment.

A successful Talos validation remains a useful additional test, but is not the
well-formedness premise of the correctness theorem.

## Work breakdown

### W0: freeze the semantic ABI

This is the serial gate for all later work.

Deliverables:

- add `f32` and `f64` physical types;
- introduce `AbiKind` and total checked conversion from impure `Expr` types;
- retain ABI kinds in locals, signatures, imports, and runtime operations;
- specify erased, void, tagged, tobject, and reuse-token encodings;
- define deterministic runtime-import identities and ordering;
- define handle encoding and decoding relations;
- define target resource failures and structured traps;
- introduce an explicit `WasmSupported` or `AbiWellFormed` predicate; and
- add guards for every impure type and runtime-operation signature.

Cross-track dependency: FIR's abstract scalar runtime does not yet model
`Float` or `Float32`. Record the gap and coordinate any shared runtime change
through the integration owner; do not create a private Wasm-only source value.

Definition of done:

- no known impure type silently maps to the wrong physical type;
- encode/decode round trips are tested for every supported ABI kind;
- aliases retain stable handles;
- every runtime operation has a checked semantic signature; and
- `make check` passes in the worktree.

### W1: harden the adapter and checker

This can proceed in parallel with W2 after W0 is frozen.

Deliverables:

- implement the complete symbolic checker;
- preserve a source map from Talos indices to FIR imports/functions;
- check import and function index resolution;
- check local and label depth conversion;
- reject unsupported initializer and closure cases explicitly;
- run Talos's validator as an additional smoke check; and
- add negative fixtures for unknown locals, labels, calls, and bad stack
  shapes.

Definition of done:

- every module accepted by the adapter first passes FIR validation;
- malformed symbolic fixtures fail with specific errors; and
- adapter tests cover imports, direct calls, nested blocks, cases, and jumps.

### W2: implement the first semantic host runtime

Start with the operations required by constructor control flow:

1. natural and string literals;
2. constructor allocation;
3. object projection; and
4. constructor tag lookup.

Deliverables:

- `Codec.lean` for typed value/handle conversion;
- `Runtime.lean` for `RuntimeHost`, structured traps, and host functions;
- a `HostEnv` builder aligned positionally with module imports;
- explicit arity and ABI-kind checks at every host boundary; and
- abstract `HostContract`s for the first runtime operations.

Definition of done:

- every generated import has exactly one matching host resolver;
- bad handles and arguments trap with a structured source or target fault;
- concrete hosts satisfy their abstract contracts; and
- literal, constructor, projection, and tag operations execute independently.

### W3: build the differential harness

Provide one entrypoint that runs both semantics:

```lean
runDifferential :
  ImpureProgram -> Name -> Array Impure.Value -> DifferentialResult
```

It should:

1. run the FIR interpreter;
2. lower and validate the program;
3. adapt it to Talos;
4. encode entry arguments and construct the host environment;
5. execute the Talos function;
6. decode the result and host state; and
7. compare outcome, world, external trace, and reachable heap.

The W3 semantic host reuses FIR's deterministic allocator from the same empty
runtime, so the executable comparison intentionally requires equal reachable
locations. Tagged, scalar, and erased entry arguments are supported;
heap-backed arguments are rejected until the harness accepts an explicit
initial runtime. The W4 theorem states the more general address-renaming
relation.

Define a target observation that distinguishes:

- a decoded return value;
- a structured source runtime fault;
- an unexpected target trap;
- invalid Wasm; and
- runner fuel exhaustion.

Only the first two correspond to source observations. Invalid Wasm,
unresolved imports, unexpected traps, and target fuel exhaustion are backend
or harness failures for a terminating supported source execution.

First corpus:

- `abiLiteralProgram`;
- `abiCtorProjectionProgram`;
- `abiCaseProgram`; and
- `abiDefaultCaseProgram`.

These are the final-impure-ABI-correct equivalents of `literalProgram`,
`ctorProjectionProgram`, `caseProgram`, and `defaultCaseProgram`. The original
hand-built fixtures bind possibly tagged `Nat` values as heap-only `object`;
the harness records their rejection under
`FIR-BUG-wasm-none-object-nat-fixture` instead of weakening the proof
fragment.

Definition of done:

- all four ABI-correct programs produce related returns and reachable heaps;
- the harness prints enough evidence to reproduce a mismatch; and
- every possible discrepancy is routed to a Wasm bug card before a workaround.

### W4: prove the first lowering theorem

Use Talos's existing `HostSpec`, `HostEnv.Satisfies`, `wp`,
`TerminatesWith`, and `PartiallyMeets` interfaces.

Proof layers:

1. ABI encode/decode lemmas;
2. concrete runtime hosts satisfy relational contracts;
3. adapter conversion preserves locals, labels, calls, and signatures;
4. lowering preserves the call-free literal/constructor/projection/case
   fragment; and
5. the local result lifts to exported functions and program observations.

Layers 1--3 and the fuel-free executable-to-observation bridge are checked in
`FirTalos/Correctness/`. Layer 4 covers lowering and host steps for the whole
initial fragment, provides their common instruction-level host-call lifting,
and packages local loads, destination stores, complete initial-fragment let
sequences, adapter concatenation, and recursive constructor-case chains. The
compiler exposes proof equations through its `partial_fixpoint` core, while
`FirTalos/Correctness/Locals.lean` provides the source-environment/local
relation, checked-write preservation, and handle-allocation chaining needed at
each recursive boundary. The semantic layer has a common related-state/
`CodeWP` judgment, a generic direct-`let` rule, closed natural/string
literal-to-return instances, recursive constructor/projection instances, and
path-sensitive constructor/default-case composition. Layer 5 is now factored
through `SupportedExport`: the four generated fixtures share one checked
lowering/adaptation/host/export package and one fuel-free exported-correctness
theorem. `FirTalos/Correctness/Program.lean` completes the program-level
induction: one `CodeSimulation` certificate recursively composes direct lets,
selected constructor/default cases, and returns; derives the local `CodeWP`;
and derives `CodeEvaluates`. A separate soundness induction connects that
proof-facing source relation to the repository's executable `ExecEvaluates`
semantics. `SupportedExport.execCorrect_of_simulation` packages both the
executable FIR run and fuel-free correctness of the named Talos export. The
literal, constructor/projection, explicit-case, and default-case fixtures all
derive their final results through this API rather than fixture-specific
`CodeWP` recursion.

W4 is complete for this initial theorem domain. The next semantic proof slices
belong to W5.

The initial theorem excludes closures, external declarations, recursion,
ownership operations, and initialization. These exclusions must appear in an
executable supported-fragment predicate, not remain comments.

A suitable theorem shape, now realized by
`SupportedExport.execCorrect_of_simulation`, is:

```text
syntax-directed simulation certificate
  -> FIR ExecEvaluates observation O
  /\ generated Talos export TerminatesWith an observation related to O
```

For programs whose termination is not yet proved, use `PartiallyMeets` rather
than exposing raw fuel in public statements.

### W5: expand the semantic backend

Add vertical slices in this order:

1. `usize` and scalar projections;
2. boxing, unboxing, and `isShared`;
3. object, scalar, and `usize` mutation plus `setTag`;
4. `inc`, `dec`, and deletion;
5. reset and reuse;
6. external calls with world and trace;
7. initialization and global caching; and
8. closures, indirect dispatch, and recursion.

Each slice includes runtime functions, contracts, differential examples, and
an extension of the supported-fragment theorem. Do not mark ownership or
reuse complete using an observational no-op runtime.

W5.1 is complete. `usizeProj` and `scalarProj` now resolve to semantic host
operations, reproduce the source projection operations and structured faults,
and preserve the runtime and opaque-handle table on success. Exact host-step,
instruction-stack, destination-local, `LetStepSimulates`, and recursive
`CodeWP` rules cover both operations. The scalar rule exposes the required
dynamic invariant explicitly: the stored `ScalarValue` must encode and decode
at the declaration's result kind; the layout `width` is not a type width.

The executable supported gate accepts `uproj` only at `USize` and accepts
`sproj` only at the four integer scalar kinds represented by the shared
runtime. Float projection remains tracked by
`FIR-BUG-wasm-none-float-runtime-gap`. Regressions cover a successful
compiler-shaped USize projection, exact scalar missing-field agreement, and a
successful pre-populated UInt32 scalar host projection. W5.3 now supplies the
closed successful compiler-shaped scalar fixture: constructor allocation
reserves scalar storage and `sset` initializes its typed value before `sproj`.

W5.2 is complete. Boxing reconstructs the exact canonical impure integer or
`USize` type from the ABI kind, so large heap boxes retain the same observable
type metadata as FIR. Boxed results use `tobject` in the proved fragment
because the runtime representation depends on the payload; unboxing and
`isShared` return direct scalar lanes without changing the handle table.
Host-step, instruction-stack, local-binding, and `LetStepSimulates` rules cover
all three operations, including allocation-side handle extension for boxing.

The shared `isShared` contract was repaired first in its own integration
commit: Lean 4.32's `ExpandResetReuse` emits `UInt8`, and FIR now agrees while
scalar case discriminants continue through `getTag`. This resolves
`FIR-BUG-wasm-none-isShared-abi-drift` and corrects the historical account in
`FIR-BUG-impure-isShared-bool-representation`. Differential regressions cover
small tagged and maximum-width heap boxing, round-trip unboxing, reachable
boxed heap evidence, and both tagged/shared and unique-heap `isShared`
results. Floating-point boxing remains gated by the shared runtime gap.

W5.3 is complete. `objectSet`, `usizeSet`, `scalarSet`, and `setTag` resolve to
semantic host operations, mutate the same FIR runtime state as the source
interpreter, return no physical values, and preserve the opaque-handle table.
The supported gate requires an exact heap-object lane for mutation targets,
checks object-field/refined scalar kinds, and verifies that the `sset` type
annotation agrees with the stored scalar lane.

The proof stack adds transparent recursive-compiler equations, exact host-step
and host-contract simulations, compiler/adapter composition rules, and a
no-result stack transformer. `SourceEffectResult`, `EffectStepSimulates`, and
`CodeSimulation.effect` extend the shared program induction without encoding
mutation as a fake `let`; operation-specific rules cover all four effects.
Differential regressions exercise a compiler-shaped layout containing object,
`USize`, and UInt64 fields, a projected object-field overwrite, and tag
mutation followed by case selection. No semantic discrepancy or new bug card
was found in this slice.

W5.4 is complete. Nonpersistent `inc` and `dec` and explicit deletion now use
semantic host operations backed by FIR's reference-count runtime; persistent
increments and decrements are proved source/target control-flow no-ops, exactly
matching the executable lowerer. All operations return no physical result and
preserve the handle table while updating liveness and reference counts in the
shared runtime.

The W5.3 effect induction is reused unchanged. Transparent compiler equations
and adapter rules cover emitted and elided ownership instructions; unary-host
and elided-effect semantic rules instantiate `EffectStepSimulates` for each
case. Differential regressions cover an increment/decrement round trip,
persistent elision, and deletion followed by the exact `deadObject` source
fault. No new bug card was required.

W5.5 is complete. Reset returns an opaque `reuseToken` handle after performing
the source runtime's uniqueness check, released-field decrements, and slot
clearing. Reuse decodes that token plus replacement object fields and either
updates the unique constructor location or allocates a fresh constructor when
the token is empty. Result handles preserve heap aliases without exposing FIR
locations in the physical ABI.

Exact host-step and handle-invariant simulations cover both operations;
compiler equations, stack/local composition, and `LetStepSimulates` rules bind
tokens and reused objects through the existing recursive program theorem.
Differential regressions cover both the unique in-place path and the shared
fallback-allocation path, including header replacement. No semantic mismatch
or new bug card was found.

W5.6 is complete. Symbolic external imports retain their original Lean
parameter and result types alongside the semantic ABI, and validation rejects
missing or inconsistent metadata. The Talos resolver now installs a
first-class external host operation instead of rejecting the import. Each run
selects an `ExternalImpl` in `RuntimeHost`; successful calls decode arguments,
reuse the source interpreter's `resumeExternal` transition, encode the result,
and therefore preserve the exact heap, next-location, world, and trace policy.
External failures remain structured FIR source faults.

The supported gate admits only exact calls to declared externals with
compatible non-void argument and singleton result kinds; internal direct calls
remain reserved for the closure/dispatch slice. The proof boundary includes
an exact host-step equation, a generated-stack call rule, a complete
argument-load/call/local-bind composition rule, the source interpreter's
three-step external-let judgment, and `ExternalLetStepSimulates`. Differential
`codeWP_externalLet` composes that step with an arbitrary proved continuation,
and `SupportedExport.execCorrect_of_externalLet` lifts one checked external
prefix plus the existing call-free fragment to executable source and fuel-free
target correctness. Regressions cover both a successful echo call—including
world and trace—and the reject-by-default fault path. No semantic mismatch or
new bug card was found.

### A0: emit the first host-backed Wasm artifact

A0 is an independently assignable artifact lane. It can run in parallel with
W4 because it consumes the checked output of `Fir.Wasm.lower` and the W2 host
contracts without changing either one. Its first result is intentionally a
demonstrator for the initial semantic fragment, not the W6 production runtime.

Deliverables:

1. serialize the validated symbolic instruction subset to standard WAT or a
   `.wasm` binary, with a deterministic command-line entry point;
2. preserve import module/name pairs, signatures, function indices, and
   exports exactly as checked by FIR and exercised by the Talos adapter;
3. provide an external-engine host shim for the W2 `fir.*` imports using the
   same opaque-handle behavior and structured failure boundary;
4. run the four W3 ABI-correct literal/constructor/projection/case programs in
   that engine; and
5. compare decoded returns and observable runtime state with the existing W3
   differential oracle, recording every discrepancy as a Wasm bug card.

Lane boundary and ownership:

- prefer new emitter modules under `Fir/Wasm/Emit/` and isolated runner/tests
  under `integration/talos/artifact/`;
- do not edit `Fir/Wasm/ABI.lean`, `Fir/Wasm/Lower.lean`,
  `Fir/Wasm/WellFormed.lean`, or `FirTalos/Correctness/` in the A0 branch;
- do not add a second ABI, locally reinterpret handles, or silently accept a
  program rejected by `lowerSupported` or `validateModule`;
- route any required root build-target or shared-contract change through the
  integration owner as a separate commit; and
- report the chosen external engine and encoder, including their pinned
  versions and licensing consequences, before making them required tooling.

Definition of done:

- one deterministic command produces an artifact from every program in the
  initial W3 corpus;
- an independent standards-conforming engine validates and executes it;
- the four decoded outcomes agree with W3, including reachable heap evidence;
- malformed or unsupported modules fail before emission with specific errors;
- emitted artifacts are reproducible byte-for-byte (or text-for-text for the
  initial WAT checkpoint); and
- `git diff --check`, `make check`, `make talos-check`, and the lane-local
  external-engine tests pass.

A0 hands back an emitter API over a validated `Fir.Wasm.Module`, an artifact
CLI, the isolated host shim, and engine-level regression evidence. W4 may use
that evidence as testing support, but no W4 theorem depends on the external
engine or serializer.

### W6: refine to a concrete runtime

Once the semantic backend is stable, introduce a separate concrete target:

- choose wasm32 or wasm64 and fix pointer-width semantics;
- specify tagged values and heap layout in linear memory;
- implement allocation, fields, closures, and reference counts;
- relate concrete addresses to FIR locations and semantic handles;
- prove each concrete runtime operation refines its W2 contract; and
- compose that refinement with the lowering theorem.

Binary encoding and production ABI compatibility begin here, not in W0.

## Parallel agent packages

After W0 lands, use file-level ownership to minimize conflicts:

| Package | Primary files | Dependencies |
|---|---|---|
| ABI and validation | `Fir/Wasm/ABI.lean`, `Fir/Wasm/WellFormed.lean` | W0 gate |
| Symbolic lowering | `Fir/Wasm/Lower.lean`, lowering fixtures | frozen ABI |
| Talos adapter | `FirTalos/Adapter.lean`, adapter fixtures | frozen ABI |
| Host codec/runtime | new `FirTalos/Codec.lean`, `Runtime.lean` | frozen ABI |
| Contracts/proofs | new `FirTalos/Contracts.lean`, `Correctness/` | codec and adapter APIs |
| Differential tests | new `FirTalos/Differential.lean` | adapter and runtime |
| A0 artifact emission | new `Fir/Wasm/Emit/`, `integration/talos/artifact/` | W1 checker, W2 contracts, W3 corpus |

Only one package owns an existing shared file at a time. Prefer new modules
for contracts, fixtures, and proofs. If an agent discovers that the frozen ABI
must change, stop dependent work and route a standalone contract commit
through integration rather than letting branches drift.

## First milestone

The first milestone is complete when:

- W0 ABI kinds and encoding rules are frozen;
- the symbolic module passes FIR validation;
- the four constructor/case programs execute in Talos;
- returned values, runtime world/trace, and reachable heaps match FIR;
- the concrete host functions satisfy abstract Talos host contracts;
- a checked theorem covers the restricted call-free fragment;
- `git diff --check`, `make check`, and `make talos-check` pass; and
- all discovered discrepancies have bug-card IDs.

## Integration and handoff

Commit small green vertical slices. Rebase on local `main` after every shared
contract lands and before handoff; never merge `main` into this branch.

Each handoff reports:

- base and head commits;
- completed W-stage slice;
- files and shared contracts changed;
- exact checks and results;
- Wasm bug-card IDs, or `none`; and
- known follow-ups.

The worktree must be clean at handoff.

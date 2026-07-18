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
| 2026-07-17 | A0 scalar Boolean results | validation and integration owners | landed | `nat-list-nonempty-bool` exposed `FIR-BUG-impure-none-bool-result-scalar`: Lean 4.32 returns `Bool` as scalar `UInt8`, while validation accepted only tagged objects. Shared commit `f9cdeb2` admits exactly scalar zero/one in LCNF observations; the Wasm schema and V8 decoder now mirror that boundary. The native↔LCNF and native↔V8 matrices retain nonempty/true and empty/false cases as regressions. |
| 2026-07-18 | A0 W5 manifests and host | proof, concrete-runtime, and integration owners | landed | Commits `9ec5b43`, `29986dd`, and `3ed7432` serialize the W5 semantic-import vocabulary, keep captured source dependencies internal, and implement projection, boxing/sharing, mutation, ownership, and reset/reuse in the shared Node host. The default native↔V8 matrix grew from 13 to 15 compiler-produced cases. No shared semantic contract changed. |
| 2026-07-18 | A0 W5 calls and effects | proof, concrete-runtime, and integration owners | landed | Commit `c1ff015` completes the artifact adaptation for cache operations, exact semantic externals, closure metadata, and generated direct, recursive, saturated, and underapplied calls. The default native↔V8 matrix now checks 21 compiler-produced cases; the independent Talos↔V8 lane checks 34 exact fixtures, including external world/trace effects and one-miss/two-call lazy caching. Legacy `closureApply` remains outside the W5 generated backend by design. No shared semantic contract changed. |
| 2026-07-18 | A0 large-Nat JSON boundary | validation and integration owners | carded | `FIR-BUG-wasm-none-json-nat-precision` records that the version-1 corpus protocol encodes arbitrary `Nat` datums as JSON numbers, so Node cannot audit odd values above `2^53` exactly. Small `Nat.add` is retained in the default matrix; large odd cases fail closed rather than weakening the audit. |
| 2026-07-18 | A0 heap-backed source/results | validation and integration owners | landed | Commits `a448442`, `5880c92`, and `32d1ed7` generate and execute compiler-produced Unicode string, signed-integer, and byte-array identity programs. Initial-runtime manifests and the shared host now reconstruct decimal-string heap integers and exact byte arrays; V8 result decoding covers positive/negative immediate integers, both 32-bit boundaries, the first positive/negative heap integers, and boundary bytes. The default native↔V8 generation matrix grew from 21 to 29 cases. No W6/proof file or shared semantic contract changed. |
| 2026-07-18 | A0 ByteArray externals | validation and integration owners | landed | Commits `5c32509` and `73fad11` generate and execute `ByteArray.size`, boundary-index `ByteArray.get!`, and both `ByteArray.set!` ownership paths. Unique mutation reuses its heap cell; shared mutation preserves the original and allocates the updated copy. The default native↔V8 generation matrix now checks 35 compiler-produced cases. No W6/proof file or shared semantic contract changed. |
| 2026-07-18 | A0 Int literal externals | proof and integration owners | landed | Commit `2426311` generates and executes compiler-emitted `Int.ofNat` and `Int.neg` calls for positive and negative literals at both immediate and heap representation boundaries. The default native↔V8 generation matrix now checks 39 compiler-produced cases. `classifyInt` remains rejected by `WasmSupported` before emission because `supportedCode` admits only object-like case discriminators, while `Int.decLt` returns `UInt8`; its external declaration itself is already admitted. A0 did not bypass or weaken that proof-owned boundary. No W6/proof file or shared semantic contract changed. |
| 2026-07-18 | A0 final-twelve preflight | proof and integration owners | prepared | Commit `1174eaa` makes the validation external registry an explicit replay-audited tool and implements exact `Int.decLt : tobject → tobject → UInt8` behavior across both immediate/heap signed boundaries. All seven distinct source declarations underlying the final twelve cases still fail closed at `WasmSupported`: `branchNat`, `selectScalarChoice`, and `classifyInt` need scalar-case admission; `PackedPoint.setX`, `tupleRotate`, `Assoc.reassoc`, and `changeOrGrow` need `jp`/`jmp` admitted by both `supportedCode` and `closureFlowSafeCode`. The existing W5 host already covers their projection, ownership, mutation, deletion, tag, reuse, call, and structured-result operations, so no other generation-side runtime primitive is currently missing. No W6/proof file or shared semantic contract changed. |
| 2026-07-18 | A0 scalar-case admission | integration owner | ready | ABI-aware case lowering now retains `getTag` for object-like discriminators and compares compiler-produced `UInt8` discriminators directly, with separate 32-bit and 8-bit constructor-tag bounds. The symbolic validator requires both `i32.eq` operands to carry equivalent semantic lanes. Structural adaptation and Talos weakest-precondition lemmas cover the direct scalar sequence. `branch-nat`, `branch-nat-false`, `scalar-enum-cases`, and all four immediate/heap `int-classify-*` cases pass a targeted native↔V8 run. That run exposed and fixed `FIR-BUG-wasm-none-bool-argument-scalar` by normalizing protocol Boolean tags to the checked `UInt8` parameter ABI. The integration owner still needs to add these seven IDs to the root-owned default matrix; no runtime import or semantic ABI kind changed. |
| 2026-07-18 | A0 typed and guarded reset joins | integration owner | partial | Join scope, result kinds, arity, argument ABI refinement, and conservative closure flow are now checked before `jp`/`jmp` lowering. `ExpandResetReuse`'s exceptional erased argument is admitted only with `isShared(object)` provenance, a `Bool.true` path fact, and a use-site proof that the join parameter is consumed solely in the companion false arm; the live join local is represented as `object`, without widening `AbiKind.refines`. `packed-preserve` and `reuse-assoc` pass native↔V8. Negative fixtures reject unknown joins, arity/kind mismatches, unguarded erased values, and fake Boolean guards. `FIR-BUG-wasm-none-join-erased-tobject` tracks the remaining representation-polymorphic fast argument in `tuple-rotate`; `FIR-BUG-impure-expandResetReuse-delete-erased` blocks both `changeOrGrow` cases on a shared runtime contract discrepancy. No shared contract changed in this slice. |

Shared-contract changes in these A0 slices are the additive common
`nat-list-nonempty` case in `09d3c06` and the scalar-Boolean observation
boundary plus regression case in `f9cdeb2`. The runtime step semantics and
`AbiKind` vocabulary are unchanged. W4 has repaired and proved the
natural-literal invariant; A0's former rejection regression is now a successful
source-to-engine test and the bug card is fixed.
A0 has separated module generation from fixture invocation and covers all
unsigned integer and `USize` parameter kinds with explicit ABI schemas. Its
initial-runtime manifest uses the same value, heap-cell, and heap-object JSON
vocabulary as the FIR observation oracle. The W5 semantic-import vocabulary is
fully adapted in the shared host and manifest, including ownership, effects,
caches, generated calls, and immediate/heap `Int` literal construction.
The validation registry's exact immediate/heap `Int.decLt` behavior is now
exercised by all four classification cases. A targeted native↔V8 run also
covers both scalar Boolean branches and the three-way nullary enum; these seven
cases await only the root-owned default-matrix list update.
Independent A0 work can now broaden
schema-directed results and initial-runtime encodings whose compiler-produced
LCNF is already inside the supported fragment. Typed/direct-object join paths
are now covered; representation-polymorphic reset arguments and erased `del`
semantics remain explicit coordinated follow-ups, alongside the large-`Nat`
JSON protocol fix.

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

### Closures use a Wasm-level trampoline

Talos host functions cannot call back into a Wasm-defined function. Therefore
the legacy `closureApply` import is not the implementation of LCNF
closures: delegating it to the FIR interpreter would make the backend theorem
circular.

The selected design is a generated Wasm-level trampoline. A closure remains a
semantic heap value with its target name, total arity, and heterogeneous fixed
arguments. Host calls may allocate that value, compare its metadata, and
project a typed capture, but they never invoke a Wasm function. For every
statically possible target, the lowerer emits a metadata test and typed capture
projections. An underapplied branch allocates a new semantic closure containing
the old captures followed by the new arguments; a saturated branch invokes the
target through an ordinary Wasm direct call. Direct recursion therefore also
uses ordinary Wasm calls.

The current proved fragment tracks closure provenance through local `pap` and
closure-application chains. Its executable flow gate rejects oversaturation
and application of closures arriving through unknown parameters. This keeps
every generated projection and target call statically typed while leaving a
future function-table or uniform boxed convention available as a wider ABI,
not as a prerequisite for W5 correctness.

### Initializers use source-compatible lazy caching

`Fir.Wasm.Module.initializers` records only zero-argument declarations that
are actually called from generated code. Each declaration receives a mutable
`i32` initialized flag and one mutable physical value global. A call checks
the flag, evaluates the declaration on a miss, records the value in both the
shared semantic runtime and the Wasm global, then loads the cached lane. A hit
loads the value directly. There is no Wasm start function and no eager
execution of ordinary zero-argument entrypoints.

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

W5.7 is complete. The backend implements source-compatible lazy global
evaluation rather than eager Wasm initialization. The lowerer discovers only
called zero-argument declarations, assigns deterministic flag/value global
pairs, emits a conditional miss path, and records the semantic value through
the new `cacheSet` runtime operation before writing the physical lane. The
validator checks cache declarations and global kinds; the Talos adapter
allocates zero-initialized mutable globals; and the binary emitter serializes
the global section plus `global.get` and `global.set` instructions.

The proof surface fixes the exact compiler equation and adapter mappings,
proves the semantic cache host step, provides cache-set and hit/miss Talos WP
composition rules, distinguishes the source interpreter's three-step hit and
four-step miss protocols, composes both through `CodeWP`, and exposes
`SupportedExport.execCorrect_of_lazyLet`. A differential regression calls a
zero-argument external twice and checks one external event, one world update,
one semantic global, and equal returned values; a binary regression checks
that the generated global-bearing module encodes successfully. This resolves
`FIR-BUG-wasm-none-zero-arg-initializers`; no new bug card was required.

W5.8 is complete. Internal direct calls lower to ordinary Wasm calls, including
recursive targets. Partial applications allocate semantic closure objects;
closure-valued `fvar` applications use the generated Wasm-level trampoline
described above, which compares target/arity/fixed-count metadata, projects
heterogeneous captures at their declared ABI kinds, either allocates an
underapplication or invokes the saturated target, and leaves the legacy
host-callback operation outside the supported fragment. The executable closure
flow gate admits statically tracked local chains and rejects oversaturation or
unknown closure provenance before lowering.

Exact host-step equations and WP rules cover closure allocation, metadata
matching, and capture projection. Transparent compiler equations expose `pap`
and trampoline lowering, while the interprocedural source-call relation and
checked-export theorem compose any finite internal-call execution with a proved
continuation without exposing fuel in the public boundary. Differential
regressions cover ABI-correct direct calls, one captured argument, genuine
underapplication followed by saturation, and recursive list traversal; a
negative regression checks that oversaturation remains rejected. All generated
modules also pass binary encoding. No semantic mismatch or new bug card was
found.

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

#### W6.0: frozen concrete representation contract

The selected target is `wasm32-lean64`. Linear-memory addresses and all
object-like function lanes are `i32`, retaining compatibility with the W5
lowerer and the standards-conforming Node/V8 artifact lane. Source `USize`
remains `i64`: the final-impure LCNF in this repository is captured from the
64-bit Lean 4.32 toolchain, and changing `USize` to `i32` would change source
semantics rather than merely concretize the existing ABI.

LCNF scalar operations compute byte addresses from a count of pre-scalar
slots. To preserve that 64-bit data model with wasm32 addresses, every object
or `USize` constructor slot occupies eight bytes. An object word is stored in
the low four bytes of its slot and the high four bytes are zero; a `USize`
occupies the full slot. Packed scalar bytes begin at
`headerBytes + 8 * (objectFields + usizeFields)`, and the LCNF scalar byte
offset is added unchanged.

Object words use their low bit as the immediate tag. Zero is the erased/empty
reuse-token sentinel, odd words contain an unsigned 31-bit payload, and
nonzero eight-byte-aligned words are heap addresses. Semantic tagged naturals
above `2^31 - 1` are represented as persistent heap naturals. This is a
representation refinement: the source value remains tagged and ownership
operations must retain tagged-value behavior for the promoted object.

Every heap allocation begins with a self-describing 32-byte header:

| Byte | Field |
|---:|---|
| 0 | object-kind code |
| 4 | persistent/live flags |
| 8 | reference count |
| 12 | aligned allocation size |
| 16, 20, 24, 28 | four kind-specific auxiliary words |

Constructor auxiliaries record tag, object-field count, `USize`-field count,
and packed scalar bytes. Closure auxiliaries record function-table index,
arity, fixed count, and the static capture-descriptor index. Closure captures
use one eight-byte slot apiece; their `AbiKind` descriptor fixes which four or
eight bytes are live. Freed allocations retain a dedicated header kind so
invalid/dead-object accesses can produce structured faults rather than depend
on host traps.

`Fir/Wasm/Concrete/Layout.lean` is the executable source of truth for these
constants and offset calculations. `Fir/Wasm/Concrete/Refinement.lean`
introduces the proof-only bijection from semantic locations to concrete
addresses, the disjoint mapping for promoted tags, and an ABI-indexed
`ValueRel`. `ValueRel` fixes the concrete lane and semantic value together and
proves agreement with the W0 physical ABI. Executable guards cover boundary
immediates, mixed object/`USize`/scalar constructor offsets, and heterogeneous
closure captures.

This is deliberately not the native Lean wasm32 C layout: native wasm32 would
make `USize` and LCNF pre-scalar slots 32-bit. Supporting that ABI requires
capturing LCNF under a genuine wasm32 data-layout configuration and is a
separate target, not an unchecked reinterpretation of the current program.

#### W6 implementation slices

1. W6.1 adds checked little-endian linear memory, allocation, header
   encoding/decoding, immediate or promoted natural literals, constructors,
   projections, and cases. Each operation proves refinement to its W2
   semantic contract before its host import is replaced.
2. W6.2 adds packed scalar and `USize` fields, boxing/unboxing, mutation, and
   tag updates.
3. W6.3 adds reference counts, deletion, reset, and reuse, including recursive
   release and both reuse paths.
4. W6.4 adds concrete closure allocation, capture projection, dispatch
   metadata, direct/recursive calls, and globals.
5. W6.5 adds externals, world/trace behavior, and structured source/target
   fault encoding.
6. W6.6 composes every operation refinement with the W5 lowering theorem,
   switches the generated artifact lane to the concrete runtime, and extends
   native/LCNF/Talos/V8 differential validation across the supported corpus.

Each slice keeps the semantic Talos runtime as the executable oracle. A
semantic discrepancy receives a Wasm bug card before the concrete runtime is
weakened or the source contract is changed.

W6.0 is complete. The target/data-model decision, tagged-word split, promoted
tag policy, common header, constructor/capture offsets, and ABI-indexed value
refinement are executable Lean definitions with boundary guards and basic
representation theorems. No W0/W2 shared contract changed.

W6.1a is complete. `Fir/Wasm/Concrete/Memory.lean` adds checked little-endian
`UInt32`, `UInt64`, and object-word loads/stores; page-sized zero growth; a
monotone eight-byte-aligned allocator; exact common-header encoding/decoding;
and live-header validation that distinguishes bounds, address-space,
alignment, kind, malformed-header, and dead-object target failures. Executable
regressions cover maximum-width round trips, exact bounds failure, a decoded
constructor header, and memory growth. Constructor payload operations and
their semantic refinement are the next W6.1 slice.

W6.1b is complete. The concrete runtime encodes small tags directly and
allocates persistent natural objects for tags above the 31-bit wasm32 payload
range. Empty constructors use that same tagged path; allocated constructors
write exact headers and zero-padded eight-byte object slots, leave `USize` and
packed scalar storage initialized to zero, and provide checked tag, object,
and `USize` projections. Large source naturals use little-endian 64-bit limbs
in ordinary reference-counted allocations. Source arity/type/bounds failures
remain distinct from concrete memory failures.

The value-refinement witness now has explicit location binding and promoted-tag
extension lemmas. Immediate encoding has an exact operation equation and
`ValueRel` theorem; new heap locations and promoted tags have direct result
relations. Executable differential coverage allocates the same mixed
constructor in the semantic and concrete runtimes and compares its tag and
projected field. The remaining W6.1 proof slice must relate the decoded heap
contents and allocator extension, then lift constructor allocation/projection
to the W2 host contracts before any semantic import is replaced.

W6.1c establishes the decoded live-heap proof boundary. Allocation descriptors
record constructor field kinds, promoted payloads, or large-natural values as
ghost metadata; they are paired with the semantic-location/address bijection
but never stored as source data. `LiveCellRel` now covers exactly concrete
constructors and large naturals, `PromotedTagRel` accounts for concrete-only
persistent tag allocations, and bidirectional `LiveHeapRel` requires every
mapped live semantic cell to have a decoded concrete implementation and every
concrete mapping to name the corresponding semantic cell.

Projection theorems extract a typed `ValueRel` from a related constructor for
object fields and an exact `USize` relation for `uproj`. Result-extension
theorems cover fresh constructor and natural addresses. Large-natural decoding
reconstructs the original arbitrary `Nat` from its little-endian limbs. The
next proof step is preservation: prove the checked allocator and payload
writes extend `LiveHeapRel`, then package those results as concrete refinements
of the W2 allocation/projection contracts.

W6.1d has started with the verified word-access layer. Checked `UInt32`
writes now have a proved byte-level postcondition: memory size is preserved,
the four little-endian bytes decode to the original lane, and every other byte
is framed. Successful same-address reads and disjoint 32-bit reads follow from
that postcondition. `UInt64` accesses are implemented and proved as two
adjacent verified 32-bit lanes, including exact round trips and a disjoint
32-bit frame rule; concrete `Word32` object lanes inherit the same round-trip
guarantee. Common headers are now structurally written as eight adjacent lanes;
their generic sequence postcondition proves every indexed word, unchanged
memory size, disjoint-read framing, and exact `Header.write`/`Header.read`
round trips. Successful monotone allocation now has an exact postcondition for
the grown memory, aligned address/cursor, wasm32 address-space bound, heap-word
classification, and in-bounds extent. Object allocation composes that result
with the header proof and passes the complete checked `readLiveHeader` path.
The live-heap boundary now also carries an aligned, in-bounds allocation
frontier whose unused suffix is byte-for-byte zero. Initial memory satisfies
that invariant; page growth, allocation, and in-prefix header installation
preserve it, with a byte-level header frame theorem. This makes the claimed
zero initialization of `USize` and packed-scalar storage explicit rather than
an ambient-memory assumption. Object-field installation now has an exact
inductive postcondition: every object word and zero high-padding lane reads
back, memory size is unchanged, and disjoint words and bytes are framed. Its
composition with object allocation preserves the checked header and frontier
and certifies that the untouched `USize`/scalar suffix remains zero. The next
step packages the concrete `allocateConstructor` result as a
`ConstructorObjectRel` and then a `LiveHeapRel` extension.

W6.1e completes the first of those two packaging steps. A successful public
nonempty `allocateConstructor` now decomposes into the exact checked object
allocation and object-field writer used by the lower-level preservation
theorems. Under the constructor metadata bounds and pointwise field
`ValueRel`, its result preserves the zero frontier and satisfies
`ConstructorObjectRel`: the decoded header, semantic tag, field arities,
typed object projections, and zero-initialized `USize` projections all agree.
The remaining W6.1 preservation step is deliberately global: strengthen the
live-cell boundary with allocation extents, use fresh-allocation framing to
retain every old mapped cell, and extend `LiveHeapRel` with the new constructor
without assuming that unrelated heap bytes are immutable.

W6.1f establishes that fresh-allocation frame independently of any one heap
object kind. `MemoryState.PrefixExtension` records cursor and memory-size
monotonicity together with exact byte preservation below the old owned
frontier. It is reflexive and transitive; page growth, raw allocation, common
header installation, and the complete public nonempty constructor allocation
all satisfy it. The next relation-transport proof can therefore reason from
allocation extents and this single prefix boundary instead of replaying the
header and payload writers for every old semantic cell.

W6.1g completes nonempty constructor allocation refinement at the decoded
heap boundary. Prefix transport now covers checked headers, typed constructor
projections, recursive large-natural limbs, promoted tags, every `LiveCellRel`
case, and the complete pre-allocation `LiveHeapRel`. A separate monotone ghost
witness relation preserves old location, promoted-tag, descriptor, and
ABI-indexed value relations; fresh bindings preserve witness injectivity and
address disjointness. The final constructor theorem combines those layers
with the actual semantic `allocCtor` result: it extends both heaps and the
witness, retains the bidirectional relation for every old cell, installs the
new `ConstructorObjectRel`, and relates the returned wasm32 address to the
fresh semantic location. Empty constructors remain on the already-proved
tagged/immediate path. W6.1 can now package projection and tag operations
against this postcondition before moving to W6.2 field mutation and boxing.

W6.1h closes that operation boundary for mapped live constructors. The actual
W2 semantic `getObjectField`, `getUSizeField`, and `getTag` operations now
refine the checked concrete object-word, `UInt64`, and header-tag reads through
`LiveHeapRel`; constructor descriptors select the ABI kind used by `ValueRel`,
while non-constructor live cells discharge by the matching semantic fault.
Together with the allocation theorem, this gives a compositional
allocate-then-project correctness path for every nonempty constructor. Empty
constructors continue to use the immediate tag encoding and require no heap
projection. W6.1 is complete; W6.2 begins with checked field mutation and
boxing while preserving the same heap and witness relations.

W6.2a establishes the mutable-tag object boundary. Constructor descriptors
remain allocation/layout metadata, while `ConstructorObjectRel` now relates
the header tag directly to the current semantic constructor tag; this is the
invariant required by `setTag` after allocation. The checked concrete
`writeTag` operation rewrites the canonical common header, and its preservation
theorem proves exact updated decoding while framing every object and `USize`
payload read. An executable regression mutates a mixed constructor and checks
the new tag together with both preserved payload regions. The next slice lifts
this local object theorem through a non-overlapping-allocation invariant to
the complete semantic heap, then reuses that frame for field mutation.

W6.2b adds exact checked `USize` mutation at the decoded-object boundary.
`ConstructorObjectRel` now records that the common header allocation size is
the declared `ConstructorLayout` extent, so slot-write bounds follow from the
layout invariant rather than from a previous successful read. The public
`writeUSizeField` operation validates the constructor and index, performs one
checked little-endian `UInt64` write, and preserves the header, tag, every
object projection, and every other `USize` slot. Its theorem relates the result
to the semantic array update at precisely the selected index. The executable
mixed-constructor regression checks the same frame. During this slice,
`FIR-BUG-wasm-none-handwritten-scalar-layout` recorded that the shared
hand-written scalar fixture uses operand `size` where Lean 4.32 emits
`size + usize`; concrete scalar work follows the compiler-shaped contract.

W6.2c adds the compiler-shaped packed-scalar address boundary and the first
typed scalar mutation operation. `writeScalarUInt64Field` requires the emitted
fixed-slot operand `size + usize`, validates the byte range against `ssize`,
and performs one checked little-endian write. Its local correctness theorem
proves exact `UInt64` readback while framing the constructor tag and every
object and `USize` projection. The executable mixed-constructor regression
uses operand `2`, retaining the discrepancy above as a visible guard against
the handwritten operand `1`. Packaging packed bytes as typed semantic scalar
fields, then boxing and unboxing those fields, is the next W6.2 slice.

W6.2d packages the first typed packed-field case in the decoded constructor
relation. A related semantic `UInt64` scalar field must use the emitted
`size + usize` base, fit within `ssize`, and read back exactly from linear
memory. Fresh allocation still establishes the relation vacuously; prefix
extension transports populated fields; and tag and `USize` mutation now prove
that the packed observations are framed. The checked scalar-write theorem
installs the same head-and-filter list shape as semantic `setScalarField` for
the first field, yielding a new `ConstructorObjectRel` rather than only a
byte-local readback fact. Generalizing this typed predicate to `UInt8`,
`UInt16`, and `UInt32` precedes boxing and unboxing.

W6.2e extends that boundary to packed `UInt32`. The runtime validates a
four-byte range, uses the verified little-endian 32-bit lane, and exposes
checked read and write operations. Prefix extension, header mutation, and
`USize` mutation preserve related 32-bit fields; the scalar-write theorem
installs the exact semantic head-and-filter update while framing tag, object,
and `USize` observations. A mixed-constructor regression writes the upper
four bytes of the eight-byte packed region and reads back `UInt32.max`.
`UInt8` and `UInt16` remain before boxing/unboxing.

W6.2f starts the narrow packed-lane boundary with checked `UInt8` projection.
The decoded relation now admits byte fields with exact compiler-base and
`ssize` bounds; fresh-prefix transport, tag updates, and `USize` updates prove
that those byte observations are preserved. The executable mixed constructor
reads its zero-initialized first packed byte. Byte mutation, followed by the
two-byte `UInt16` memory lane, is next; no concrete import switches to these
operations before their mutation proofs land.

W6.2g completes packed `UInt8` mutation. A checked byte store preserves memory
size, the decoded header, every object and `USize` projection, and installs an
exact semantic `UInt8` head-and-filter update. The executable regression
writes `UInt8.max` into a nonzero packed offset and checks all framed regions.
The two-byte `UInt16` lane is the remaining integer scalar representation
before W6.2 moves to boxing and unboxing.

W6.2h completes the integer packed-scalar representation with a verified
little-endian `UInt16` memory lane, checked constructor projection and
mutation, prefix transport, and preservation through tag and `USize` writes.
The scalar mutation theorem installs the exact semantic `UInt16`
head-and-filter update while framing fixed constructor slots. Executable
regressions cover unaligned `UInt16.max` memory round-trip and packed-field
mutation. All four scalar integer kinds now have concrete read/write and local
semantic refinement boundaries; boxing and unboxing are next.

W6.2i establishes the heap-backed integer boxing boundary. Box headers store a
stable five-way `UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize` code in `aux0`, the
meaningful payload width in `aux1`, zero reserved auxiliaries, and one
canonical zero-extended eight-byte payload slot. Concrete boxing follows FIR's
63-bit semantic tagged limit rather than wasm32's 31-bit immediate limit: only
larger `UInt64`/`USize` payloads allocate a reference-counted box, while the
existing tagged encoder handles direct and promoted representations.

The decoded live-cell relation now has an exact boxed-object case. Successful
heap-box allocation preserves the allocation frontier and every old decoded
cell, extends the ghost location/descriptor bijection, installs the fresh FIR
boxed cell, and relates the returned wasm32 address at `tobject`. Checked heap
unboxing validates the stored kind, width, reserved header words, allocation
extent, and canonical payload before proving agreement with FIR's stored-value
`unbox` branch. Executable regressions cover an immediate `UInt8`, a promoted
`UInt32.max`, a genuine `UInt64.max` heap box, and semantic/concrete round-trip
agreement. The next W6.2 slice proves allocation-side refinement for the
concrete-only promoted-tag branch and then packages tagged unboxing; no runtime
import switches before that full representation split is covered.

W6.2j completes that split. The promoted-tag allocator now has checked
decomposition, prefix framing, frontier preservation, exact persistent-natural
header/decoder facts, witness well-formedness, and a `LiveHeapRel` theorem that
leaves the semantic heap unchanged. `encodeTagged` composes direct wasm32
immediates with promoted allocation, and public boxing agrees with FIR across
the entire semantic tagged range. Tagged unboxing proves the same typed result
for both representations.

The proof exposed `FIR-BUG-wasm-none-promoted-tag-aliasing`: the original ghost
map stored only one address per payload, but repeated concrete encoding
allocates distinct immutable objects. Promoted tags are now modeled by
many-address membership, preserving both old `ValueRel`s and equal-payload
re-encodings. Executable and proof regressions cover the repeated allocation.
The next W6.2 slice proves `isShared` for immediate, promoted, and ordinary
heap representations before reference-counting work begins.

W6.2k completes that sharing boundary. The checked concrete operation returns
Lean 4.32's direct `UInt8` ABI result, treats direct and promoted tagged values
as shared, and reads ordinary heap persistence/refcount metadata from the
validated live header. The full `tobject` theorem proves agreement with FIR
for every currently represented live cell and relates the result at `uint8`.
Executable guards cover immediate/shared, promoted/shared, and fresh
heap/unique outcomes. W6.3 can now make refcount transitions concrete and
reuse these header-level sharing facts.

W6.3a starts the ownership transition boundary with checked increments.
Direct and promoted tagged references preserve FIR's checked no-op/unchecked
`expectedHeapReference` behavior. Ordinary heap increments decode the live
header, ignore persistent objects, reject `UInt32` overflow as a structured
target failure, and rewrite only the common header.

The local boxed-cell theorem preserves its canonical payload decoder and
rebuilds `LiveCellRel` at the incremented semantic count; a companion theorem
reduces FIR's `incValue` to the same `setCell` update. This work found and fixed
`FIR-BUG-wasm-none-constructor-refcount-frozen`: immutable constructor payload
refinement had accidentally retained the fresh-allocation count of one.
Allocation still returns the exact initialized header, while mutable live-cell
refinement now owns the count equality. Executable guards cover boxed
`1 + 2 = 3`, the resulting sharing transition, both tagged representations,
and the checked `UInt32` overflow boundary. The next W6.3 slice generalizes
header mutation framing to constructors and naturals before decrement,
recursive deletion, reset, and reuse are added.

W6.3b factors that write into a reusable header-level postcondition and proves
the first variable-sized payload frame. Rewriting an ordinary natural's count
leaves every recursive 64-bit limb read unchanged, reconstructs the decoded
natural `LiveCellRel`, and preserves the allocation frontier. The semantic
`incValue` equation is now stated once for every currently modeled ordinary
live cell instead of being tied to boxed scalars. An executable regression
increments the first heap natural from one to five, retains its exact decoded
value, and observes the expected unique-to-shared transition. Constructor
payload framing is the remaining increment case before decrement begins.

W6.3c completes that local increment matrix. A constructor header rewrite now
frames object words and their padding, `USize` slots, and packed `UInt8`,
`UInt16`, `UInt32`, and `UInt64` reads while retaining the exact constructor
descriptor and semantic fields. `LiveCellRel.incrementReference` packages the
constructor, boxed, and natural cases behind one theorem. The mixed-layout
executable guard increments from one to three and then rechecks its tag,
object field, `USize` field, and scalar field. With all current payload kinds
covered, W6.3 proceeds to decrement-above-one and then dead-cell/recursive
release semantics.

W6.3d adds the concrete decrement engine and proves its first successful
above-one case for boxed cells. Recursive constructor release is explicitly
fuel-indexed by the allocated prefix, marks the parent dead before visiting
children, and distinguishes address-bearing source underflow from target
memory failures. Checked/unchecked tagged decrements retain their exact FIR
behavior. Proof work found
`FIR-BUG-impure-none-decLocation-opaque-proof-boundary`: the shared semantic
`partial def` has no equation theorem, so source-side decrement, deletion,
reset, and reuse composition require an isolated proof-visible runtime refactor
on `main` before the remaining W6.3 proofs proceed.

W6.3e resolves that proof boundary at a deliberate resynchronization
checkpoint. Shared commit `587e339` replaces the opaque semantic decrement
with an extensionally equivalent fuel-indexed definition and publishes the
above-one equation. The Wasm branch rebased exactly onto that commit and
passed a full Lean Beam dependency resync, root build, and Talos build before
dependent proof work resumed. The first composed theorem now proves that a
boxed cell above one takes the same source and concrete count update and
retains its decoded payload relation. Natural and constructor above-one
framing are next, followed by the zero transition and recursive release.

W6.3f completes the nonrecursive decrement matrix. Common-header count
replacement is now factored independently of the ownership operation;
constructor fields and natural limbs prove that frame once, then increment and
decrement select their respective runtime branches around it. A uniform
`LiveCellRel` theorem covers constructors, boxes, and heap naturals, and its
source/concrete composition uses the shared semantic above-one equation.
Executable regressions decrement shared mixed constructors and large naturals
while rechecking all decoded payload regions. The next boundary is count one:
introduce dead-cell refinement, prove leaf deletion, and then lift recursive
constructor release.

W6.3g repairs the concrete count-one encoding before that relation is stated.
The invariant audit found `FIR-BUG-wasm-none-release-retains-live-kind`: the
runtime cleared liveness but retained the old live payload kind, contrary to
the frozen W6.0 freed-header contract. `Header.forRelease` now preserves only
the self-describing allocation extent and canonicalizes kind, flags, count,
and auxiliary words. A raw-header regression proves the dedicated `.freed`
encoding while the public live-header decoder reports the expected dead-object
failure. Dead-cell refinement can now target one exact representation.

W6.3h establishes that dead-cell boundary. `DeadCellRel` records the canonical
freed header, its validated retained extent, and prefix ownership without
attempting to decode stale payload bytes; it is stable under later fresh
allocations. The generic count-one leaf theorem reduces concrete release to
that relation, while boxes and heap naturals instantiate its empty concrete
child-reference premise. The matching source theorem proves their semantic
owned values contain no heap reference, and the composed theorem joins both
executions at the dead-cell update. Recursive constructor release and the
whole-heap live/dead relation remain the next slice.

W6.3i lifts that local boundary into the shape required by the whole heap.
`CellRel` now distinguishes fully decoded live payloads from canonical dead
allocations, and `LiveHeapRel` covers every mapped semantic cell instead of
deregistering released locations. Allocation, promoted-tag, projection,
boxing, unboxing, and sharing proofs transport or recover the live branch
from a successful source operation. In particular, `isShared` refinement now
requires semantic success: a mapping can legitimately denote a released
cell, and a stale reference must fault rather than regain a live-cell proof.
The next slice proves whole-heap preservation for the above-one and leaf-one
transitions before recursive constructor release folds those steps over owned
children.

W6.3j establishes the spatial frame invariant required by those whole-heap
transitions. Proof work recorded and resolved
`FIR-BUG-wasm-none-heap-refinement-allocation-aliasing`: address injectivity
alone did not show that a 32-byte header rewrite was disjoint from every other
decoded allocation. `LiveHeapRel` now records a readable complete region for
each descriptor and pairwise disjoint descriptor intervals. A shared fresh-
descriptor theorem preserves both facts when allocation starts at the exact
old frontier, and constructor, boxed-scalar, and promoted-tag allocation all
instantiate it. Ownership framing can now derive non-aliasing from the global
relation rather than accepting it as a theorem premise.

W6.3k completes the semantic/global bookkeeping half of ownership framing.
Dead `CellRel`s retain the allocation descriptor that remains associated with
their released address. A structural `replaceCell` theorem proves that
successful semantic replacement changes the target lookup and preserves every
other location; its `setCell` corollary also preserves `nextLocation`.
`LiveHeapRel.setCell_of_frames` then assembles the full postcondition from the
new target relation plus non-target concrete cell, promoted-tag, and descriptor
frames. The remaining work is purely spatial: show that one disjoint common-
header write supplies those frame premises for the above-one and leaf-one
ownership branches.

W6.3l starts that spatial discharge with a reusable allocation-frame module.
A successful header write now produces byte equality over any descriptor
interval proved disjoint by `LiveHeapRel`; typed 16/32/64-bit reads, raw and
checked headers, and recursive natural limbs lift that byte frame to decoder
equalities. Canonical dead cells, live boxed scalars, live heap naturals, and
promoted tagged objects all preserve their exact relations across the frame.
This isolates mixed-layout constructor framing as the final non-target cell
case before the common header mutation can instantiate
`LiveHeapRel.setCell_of_frames`.

W6.3m closes that first whole-heap ownership transition. Mixed-layout
constructor observations—including object and USize slots, alignment padding,
and packed 8/16/32/64-bit scalar fields—now preserve their complete decoded
relation under an allocation frame. Consequently every current live or dead
`CellRel`, as well as promoted tags and the descriptor-region/disjointness
invariant, survives an extent-preserving header rewrite. The composed
decrement-above-one theorem exposes the exact concrete common-header write,
performs the matching semantic `setCell`, frames every non-target allocation,
and reconstructs `LiveHeapRel` for the resulting runtime. Count-one release is
the next immediate whole-heap case; it reuses the same frame assembly while
changing the target to the canonical dead-cell relation.

W6.3n completes that count-one leaf case and factors its reusable boundary.
Successful canonical release now exposes the exact backing memory and
`Header.forRelease` write in addition to the dead-cell postcondition. A generic
whole-heap header-write assembler turns any extent-preserving write plus a new
target `CellRel` into the matching semantic `setCell`, deriving all ordinary,
promoted, and descriptor frames from disjointness. Boxes and heap naturals at
count one instantiate it with the canonical freed header and the semantic
zero-count/dead cell. Recursive constructor release is now the remaining W6.3
ownership case; it must compose this target release with ordered decrements of
the constructor's owned children.

W6.3o fixes the first discrepancy exposed by that recursive proof. The ABI
admits `.erased` constructor object fields and encodes them as the zero
sentinel, while the concrete recursive fold previously rejected that sentinel
after the semantic fold had skipped the erased value. Bug card
`FIR-BUG-wasm-none-recursive-release-erased-sentinel` records the mismatch.
Checked sentinel decrements are now exact no-ops, unchecked public decrements
still reject non-objects, invalid words remain errors, and a constructor
release regression covers the erased-field path. The recursive proof can now
relate each constructor field without excluding a valid ABI kind.

W6.3p strengthens the constructor refinement with the ABI fact needed to use
that field relation recursively. Bug card
`FIR-BUG-wasm-none-constructor-refinement-field-kinds` records that the prior
relation constrained only the descriptor length and therefore admitted scalar
kinds in ownership-traversed slots. `ConstructorObjectRel` now retains
`fieldKinds.all AbiKind.isObjectField = true`; allocation must establish it and
every payload/header preservation theorem transports it. The indexed
`fieldKind` theorem exposes an admissible kind for each declared slot. The next
slice can state the owned-reference decoder correspondence without an external
well-formedness premise.

W6.3q establishes that decoder correspondence. Concrete constructor ownership
enumeration is expressed as a `Fin`-indexed monadic traversal of the declared
object-slot count, preserving its existing left-to-right behavior while
exposing the bound at each read. `OwnershipValueRel` erases the physical ABI
kind only after retaining its `isObjectField` proof, and
`OwnershipValuesRel` lifts those pairs over ordered lists. The constructor
decoder theorem now returns exactly one related concrete word for each
semantic `objectFields` value in fold order. The remaining recursive step is
to show that paired folds preserve `LiveHeapRel` as heap children decrement and
tagged/erased fields take their checked no-op branches.

W6.3r connects the two public recursive-fuel policies. Bug card
`FIR-BUG-wasm-none-heap-refinement-release-fuel` records that semantic heap
coverage and concrete descriptor ownership previously had no aggregate
capacity consequence. `LiveHeapRel` now retains
`semantic.heap.length * headerBytes ≤ state.heapCursor`; semantic allocation
adds one heap entry and at least one concrete header, concrete-only allocation
only increases capacity, and ownership replacement preserves heap length and
cursor. The derived theorem proves `heap.length + 1` is no greater than the
concrete cursor-derived fuel. Same-fuel recursive simulation can therefore be
lifted to the actual public runtime entry points.

W6.3s proves the operational fuel lift on the concrete side. Any successful
`decrementReferenceOnceFuel` execution produces the identical memory state
when rerun with a larger fuel budget. The proof covers every object-class and
header branch and, in the count-one constructor case, lifts the induction
hypothesis through the full left-to-right child fold while threading each
updated memory state. Together with W6.3r's capacity theorem, this isolates
fuel policy from the remaining same-fuel recursive simulation: that proof can
use semantic heap fuel first and lift the concrete execution to the public
cursor-derived budget afterward.

W6.3t fixes the fuel-order discrepancy found while pairing the recursive
folds. Bug card `FIR-BUG-wasm-none-release-fuel-preempts-nonheap-noop` records
that concrete release previously exhausted fuel before classifying a checked
tagged or erased child, whereas semantic ownership traversal skips those
values without recursion. Checked immediates and sentinels are now no-ops at
every fuel, invalid and unchecked words retain their faults, and ordinary heap
recursion still exhausts at zero. Zero-fuel guards cover both direct no-op
representations and the retained ordinary-heap exhaustion branch.

W6.3u completes that correction for semantic tags with promoted physical
encodings. The promoted header is decoded before the ordinary-heap fuel gate,
so both immediate and promoted tags have a common all-fuel checked-no-op
theorem; zero-fuel regression coverage now includes the promoted allocation.
`OwnershipValueRel.releaseStep` then eliminates every ABI-admissible ownership
slot into exactly two cases: a semantic heap child with the matching witness
address, or a concrete checked no-op matching the semantic fold. Scalar and
reuse-token cases are ruled out by `AbiKind.isObjectField`. This is the local
per-field correspondence needed by the paired-fold simulation without
weakening the heap recursion bound.

W6.3v lifts that per-field split across the complete ownership lists.
`OwnershipValuesRel.foldlM_refines` is parametric in the recursive theorem for
one mapped heap child. Given a successful semantic child fold, it peels each
semantic step in order, invokes that hypothesis only for heap locations, uses
W6.3u's all-fuel no-op equation for every non-owning slot, and threads the
resulting concrete memory and `LiveHeapRel` through the tail. The remaining
W6.3 proof can now focus exclusively on the fuel-indexed transition for one
heap location; constructor child enumeration and fold ordering no longer
appear in that induction.

W6.3w normalizes the already-proved nonrecursive ownership cases to explicit
fuel. Concrete above-one decrement and count-one box/natural release now prove
that every positive fuel budget has the exact public-operation result; the
semantic counterparts expose the same fuel-indexed `setCell` equations.
Whole-heap wrappers reuse the existing header-write frame and return
`LiveHeapRel` for any positive explicit fuel. The recursive induction can
therefore dispatch above-one and childless count-one cells directly, leaving
only count-one constructors to assemble from parent release plus W6.3v's
paired child folds.

W6.3x completes that same-fuel recursive induction. A successful semantic
decrement now determines a live, nonzero mapped cell; above-one and childless
count-one cells use W6.3w directly. A count-one constructor first installs the
related dead parent through the verified header-write frame, then W6.3v applies
the induction hypothesis to each mapped heap child while preserving concrete
no-ops for non-owning fields. The result is a whole-heap theorem relating the
complete concrete and semantic recursive decrements at any common explicit
fuel. The remaining public-operation wrapper only needs W6.3r's semantic-to-
concrete fuel bound and W6.3s's concrete fuel monotonicity.

W6.3y closes that public recursive-release wrapper. Successful FIR
`decLocation` execution is first simulated at its heap-length fuel by W6.3x;
W6.3r proves that budget fits inside the concrete cursor-derived public fuel,
and W6.3s lifts the concrete success without changing the final memory. Thus
the checked public `decrementReferenceOnce` now preserves `LiveHeapRel` for
the complete supported constructor/box/natural ownership fragment. The final
W6.3 audit is reset/reuse and repeated-decrement packaging over this one-step
theorem.

W6.3z packages public one-step release into FIR's repeated decrement. Induction
over the requested amount composes `decrementReferenceOnce_refines` through
the concrete and semantic folds, with amount zero preserving both states and
each successful successor step preserving the stable witness mapping. The
complete checked `.dec amount` ownership path is therefore related. W6.3 now
turns to concrete deletion and both reset/reuse paths.

W6.3aa adds explicit concrete deletion. `deleteObject` accepts only an
ordinary live heap allocation, rejects immediate and promoted tagged values,
and installs the canonical freed header without traversing owned fields.
`LiveHeapRel.deleteObject_refines` frames that header write across every other
allocation and relates it to FIR `deleteValue`'s zero-count/dead update.
Executable guards cover the successful box deletion and both tagged rejection
paths. Reset and reuse are now the remaining W6.3 runtime operations.

W6.3ab adds the checked concrete reset engine and closes its empty-token
paths. Immediate and promoted tags leave memory unchanged; non-unique ordinary
heap cells run the already-verified public decrement and return word zero,
which is related to FIR's `reuseToken none`. The unique constructor path now
snapshots the requested ownership prefix, writes encoded tagged zero (word
one, deliberately distinct from the empty-token/erased sentinel), releases
the old references in order, and returns the allocation address. Executable
guards cover all three empty-token cases and the unique transition. The next
slice proves that prefix write and child fold preserve `LiveHeapRel`.

W6.3ac records the protocol invariant exposed by that unique-path proof.
`FIR-BUG-wasm-none-reset-cleared-object-protocol` shows that FIR reset installs
tagged zero even in a slot whose normal descriptor may be heap-only `.object`
or `.erased`; strict `ValueRel` correctly cannot treat that temporary word as
a normal value of either kind. The executable reset is unchanged and no ABI
relation is weakened. The proof must instead make the reset-to-reuse protocol
explicit (or establish an equivalent composed boundary) before the unique
path can claim whole-heap preservation.

W6.3ad adds the complete concrete reuse engine and proves its empty-token
allocation path. Token zero delegates to verified constructor allocation. An
address token validates a live constructor and retained capacity, zeroes the
complete old payload, writes replacement object fields, rebuilds constructor
metadata while preserving the allocation extent, and returns the same
address. Oversized replacement fails closed; the compiler's grow path already
uses delete plus fresh allocation. Guards cover fresh, in-place tag-changing,
payload-zeroing, and too-small cases. The nonempty empty-token theorem reuses
W6.1's witness extension and whole-heap allocation refinement.

W6.3ae establishes the payload-scrubbing proof boundary used by in-place
reuse. `ZeroBytesPost` proves that a successful checked zero-range write keeps
memory size fixed, reads zero at every byte of the half-open interval, and
preserves every byte outside it. The reusable success extractor lets the
later constructor proof combine this complete old-payload erase with the
existing object-field writer and final header rewrite without inspecting the
recursive implementation again.

W6.3af lifts that byte postcondition to runtime invariants. A scrub beginning
at `address + headerBytes` frames every common-header word and therefore
preserves both raw `Header.read` and checked `readLiveHeader`. When the scrub
ends before the heap cursor it also preserves `FrontierInvariant`, including
zero bytes beyond the cursor. In-place reuse can now treat payload erasure as
a verified framed transition before installing fields and replacement header
metadata.

W6.3ag closes the spatial framing obligation for payload scrubbing.
`MemoryState.AllocationFrame.ofZeroBytes` uses complete allocation-interval
disjointness to preserve every byte of any non-target descriptor region while
the target payload is erased. Together with W6.3af's header and frontier
facts, the in-place reuse proof can transport all other live/dead/promoted
relations through the scrub and focus its decoder reconstruction only on the
target allocation.

W6.3ah names the complete in-place byte transaction as
`LinearMemory.reuseConstructorMemory` without changing its operational order:
erase the retained payload, install replacement object fields, then publish
the replacement header. `ReuseConstructorMemoryPost` exposes both unpublished
intermediate memories and proves the final header/field reads, zero padding,
memory-size preservation, and a byte frame outside the retained allocation.
The composed frontier theorem carries `FrontierInvariant` through all three
writes. The next slice lifts this exact transaction through the descriptor
and reset-token protocol relations.

W6.3ai separates a reused constructor's active layout from its retained
physical allocation capacity. The invariant discrepancy is recorded and
resolved by `FIR-BUG-wasm-none-reuse-retained-capacity-relation`:
`ConstructorObjectRel` now requires the active `ConstructorLayout` to fit the
decoded header capacity rather than equal it. The complete retained extent
remains owned by `LiveHeapRel.descriptorRegion`, and allocation frames may be
restricted to the smaller logical prefix. A strict shrinking-reuse guard
checks that new metadata and fields decode while the old 56-byte capacity is
preserved. This is the capacity model required by the reset-token protocol.

W6.3aj introduces that protocol boundary without weakening normal heap
decoding. `ResetReuseProtocolRel` relates a unique reset as a paired concrete
and semantic transition whose input satisfies `LiveHeapRel`; it deliberately
does not assert `LiveHeapRel` for the temporary cleared states. The returned
nonempty token remains related through `RefinementWitness.rebindConstructor`,
which shadows the active constructor descriptor at the same address while
leaving semantic locations, promoted tags, witness well-formedness, and every
ABI value relation unchanged. The next slice proves unique reset enters this
transition relation; the following reuse slice consumes it and re-establishes
the normal whole-heap relation.

W6.3ak defines the protocol descriptor used while reset releases the old
children. `resetProtocolFieldKinds` changes exactly the cleared prefix to
`.tobject`, retains every suffix kind, preserves descriptor arity, and keeps
the object-field validity check true. Tagged zero then has its ordinary strict
`.tobject` relation in every cleared slot, while untouched suffix relations
transport through descriptor rebinding. This makes the temporary target a
normal decoded constructor under protocol-only proof metadata, so the existing
recursive decrement refinement can drive the child-release fold unchanged.

W6.3al supplies the spatial frame for reset's bulk prefix clear.
`MemoryState.AllocationFrame.ofWriteObjectFields` proves that every complete
allocation disjoint from the target's retained physical interval is byte-for-
byte unchanged, and `LiveHeapRel.allocationFrame_of_writeObjectFields_other`
discharges its bounds and disjointness from the global descriptor invariant.
The target reconstruction can now be isolated from transport of every other
live, dead, boxed, natural, and promoted representation.

W6.3am lifts that bulk prefix write through the public checked object-field
decoder. Every installed prefix slot reads back its exact word with valid zero
padding, while each slot at or beyond the written half-open interval decodes
exactly as it did before the transition. The reset target proof can therefore
split only on `index < count`: cleared slots use tagged-zero `.tobject`
relations and retained suffix slots reuse their original relations, without
unfolding the decoder or the recursive writer.

W6.3an closes the non-object half of that target reconstruction. The writer's
byte frame now derives reusable 16-, 32-, and 64-bit suffix-read laws, and a
bounded cleared prefix is proven invisible to checked `USize` plus packed
`UInt8`/`UInt16`/`UInt32`/`UInt64` projections. Reset can therefore rebuild the
protocol target by changing only its object-field clause; all header, extent,
`USize`, and scalar observations transport unchanged.

W6.3ao completes that target reconstruction. `resetProtocolObject` names the
semantic constructor immediately after its ownership prefix is cleared, and
`ConstructorObjectRel.resetPrefix` proves the concrete bulk write represents
it under the rebound protocol descriptor. Cleared slots decode canonical
tagged zero at `.tobject`; retained slots preserve their original ABI kind,
semantic value, concrete word, and value relation. The protocol state now has
a complete strict constructor relation suitable for the child-release fold.

W6.3ap carries the global spatial invariant through that same bulk clear.
`LiveHeapRel.descriptorSpatial_of_writeObjectFields` proves the target keeps
its original readable physical header and extent, transports every other
descriptor header through its allocation frame, and preserves all pairwise
allocation disjointness. This supplies the descriptor-region and disjointness
premises needed to lift W6.3ao from one target constructor to the whole heap.

W6.3aq proves the corresponding ghost-witness frame. Rebinding the target's
active constructor descriptor transports nested constructor `ValueRel`s and
leaves every live or dead cell at a distinct address related, including boxed
and natural cells; promoted tagged representations transport as well. This is
an explicit descriptor-shadowing law, not a monotone witness extension, and
therefore preserves the strict lookup semantics needed by in-place reuse.

W6.3ar lifts the cleared reset target to the complete heap relation.
`setCell_rebindConstructor_of_frames` assembles a semantic cell replacement
while changing only the target descriptor, and
`writeObjectFields_resetPrefix` instantiates it with the concrete bulk clear.
The resulting concrete and semantic intermediate states satisfy strict
`LiveHeapRel` under the protocol witness, with the frontier, all descriptor
regions, disjointness, non-target cells, and promoted tags preserved. Existing
verified decrement refinement can now drive the released-child fold.

W6.3as connects that intermediate relation to reset's exact child traversals.
`readOwnedPrefix` proves the concrete `List.range count` snapshot corresponds
in order to FIR's `objectFields.extract 0 count`, retaining an ownership
relation at each slot. `foldlM_public_refines` then composes the public checked
concrete decrement with FIR's public `decValueOnce` over those lists, carrying
`LiveHeapRel` through every successful step. The remaining unique-reset proof
is now operation decomposition and recomposition around these boundaries.

W6.3at proves that a successful unique reset enters the explicit reuse
protocol. `resetObject_refines_unique` decomposes FIR reset into its semantic
cell replacement and released-child fold, matches those steps with the
concrete prefix snapshot, bulk clear, and public decrement fold, and then
recomposes the exact concrete operation equation. The final cleared heap is a
strict `LiveHeapRel` under the protocol descriptor, and the nonempty concrete
token remains related to the same semantic location. The discrepancy card
stays open until in-place reuse consumes this protocol state and restores the
ordinary replacement-constructor descriptor.

W6.3au reconstructs the replacement constructor decoder after the complete
in-place byte transaction. `reusedConstructorObject` names FIR's exact
replacement payload, while `ofReuseConstructorMemory` combines the retained
allocation header, payload scrub, object-field write, and final header
publication. It proves strict replacement-kind object fields, scrub-derived
zero `USize` fields, empty packed scalars, the selected old-or-new tag, and an
active layout bounded by the retained capacity under the ordinary rebound
descriptor. The next slice frames this local result across the complete heap
and semantic `setCell` step.

W6.3av proves the spatial half of that complete-heap lift.
`ofReuseConstructorMemoryPost` frames every byte of a disjoint retained
allocation through the final transaction, and the `LiveHeapRel` wrappers use
descriptor disjointness to preserve all non-target headers.
`descriptorSpatial_of_reuseConstructorMemory` then publishes the replacement
header at the target with exactly the old physical extent while rebinding only
its active constructor descriptor; complete descriptor regions and pairwise
disjointness survive. The remaining step is to assemble these spatial facts,
the W6.3au target decoder, and framed non-target cell relations around FIR's
semantic `setCell`.

W6.3aw completes that relation-level assembly.
`setCell_ofReuseConstructorMemory` combines the W6.3au target decoder and
W6.3av descriptor frame with the verified frontier transaction, rebuilds the
target live cell with its retained reference count, and transports every
other live/dead cell and promoted tag through a complete allocation frame.
FIR's semantic cell replacement therefore restores ordinary `LiveHeapRel`
under the replacement constructor descriptor. The remaining reuse proof only
unfolds the public concrete and FIR operations, extracts this transaction,
and relates their returned references.

W6.3ax closes the public in-place reuse path. `reuseObject_some_refines`
checks the nonzero heap token, constructor kind, retained-capacity inequality,
field arity, and all `UInt32` metadata bounds; it then instantiates the
complete byte transaction from W6.3ah and the whole-heap replacement theorem
from W6.3aw. The concrete runtime and FIR both return the same existing
allocation/location, the rebound constructor descriptor satisfies ordinary
`LiveHeapRel`, and the returned object references are related. Together with
W6.3at's strict protocol descriptor, this supplies the reset-to-reuse
composition without weakening `.object` values, resolving
`FIR-BUG-wasm-none-reset-cleared-object-protocol`.

W6.3ay closes the final fresh-reuse corner case. For an empty constructor
layout, `reuseObject_none_refines_empty` reduces token-zero reuse to the
verified tagged encoder, so a small tag remains an immediate while a large
tag may extend the witness with a persistent promoted representation; both
refine FIR's unchanged runtime and tagged constructor result under `.tobject`.
An executable guard covers the direct-immediate path. With tagged reset,
ordinary non-unique reset, unique protocol reset, fresh empty/nonempty reuse,
and in-place reuse all covered, W6.3's successful-operation matrix is
complete; structured failure correspondence remains the explicit W6.5 task.

W6.4a freezes the executable concrete closure ABI. Generated function order
forms a deterministic dispatch table, while each closure header stores the
checked `UInt32` target id, total arity, fixed-capture count, and reserved
zero. Heterogeneous captures use the existing eight-byte `ClosureLayout` slots:
`i32`/`f32` lanes occupy the low word with checked zero padding, and
`i64`/`f64` lanes occupy the complete slot. `allocateClosure`,
`readClosureMetadata`, `closureMatches`, and `projectClosureCapture` fail
closed on unknown targets, malformed metadata, type mismatches, and bounds.
Executable guards cover allocation, metadata recovery, a successful typed
capture projection, and a nonmatching trampoline target. The next W6.4 slice
adds the proof-only closure descriptor and local decoder refinement.

W6.4b establishes that local decoder boundary. The refinement witness now
records a closure's function name, total arity, and ordered capture kinds;
fresh closure bindings extend old witness facts and preserve witness
well-formedness. `ClosureObjectRel` ties that descriptor to validated concrete
metadata and every occupied capture slot. Its `matches` and `project` theorems
show that the exact checked trampoline operations recover the declared target
and a typed `ValueRel` capture. The next W6.4 slice proves that successful
concrete allocation establishes this relation before lifting closure
allocation across the complete live heap.

W6.4c proves that allocation boundary. Each `i32`, `i64`, `f32`, and `f64`
capture lane has an exact checked write/read theorem with an eight-byte frame;
their heterogeneous bulk writer preserves the common header, recovers every
typed slot, and maintains the zero frontier. `allocateClosure_objectRel`
decomposes the public allocator, validates the dispatch id and header metadata,
extends the fresh closure witness, and establishes `ClosureObjectRel` for the
semantic capture array. The next slice adds closures to `LiveCellRel` and
transports every old mapped cell through this fresh prefix extension.

W6.4d supplies the frame machinery needed for that whole-heap lift. A public
closure allocation is now a proved `PrefixExtension`, checked metadata and
typed capture reads transport through any such extension, and
`ClosureObjectRel` is monotone in both concrete prefix growth and proof-witness
growth. This isolates the byte-level framing from the next slice's structural
addition of closures to `LiveCellRel` and its ownership/refcount cases.

W6.4e freezes dispatch identity at the whole-heap proof boundary. The
refinement witness now carries the module's deterministic generated-function
table, and every allocation-style witness extension must preserve it exactly.
This prevents a future closure-cell proof from choosing a convenient decoder
per object; the pending `LiveCellRel` case will use the one table installed for
the module.

W6.4f moves the generic closure read/prefix/witness transport lemmas into the
local correctness layer, below `HeapRefinement`. This is a dependency-only
checkpoint: it leaves the proved contracts unchanged while allowing the next
slice to import `ClosureObjectRel` into the exhaustive live-cell relation
without creating a cycle through allocation correctness.

W6.4g packages the pending whole-heap closure case behind `ClosureCellRel`.
The relation fixes every cell to the module-wide dispatch witness, exact
semantic closure object, checked capture decoder, live closure header, owned
capture extent, reference count, persistence bit, and liveness bit. Prefix
and witness transport are proved at this boundary before changing the
exhaustive `LiveCellRel` consumers; the next slice can therefore add one
structural constructor and reuse these facts throughout ownership and
reference-count proofs.

The structural audit exposed `FIR-BUG-wasm-none-closure-capture-descriptor-reserved`:
W6.4a currently writes a reserved zero in closure `aux3`, despite W6.0
assigning that word to the static capture-descriptor index required by
recursive ownership. The bug is recorded before changing the executable ABI;
the next checkpoint restores the descriptor-table contract, then closure
ownership can enter `LiveCellRel` without using proof-only metadata at run
time.

W6.4h restores that frozen descriptor-table boundary. Closure allocation now
resolves both a generated target id and a generated capture-descriptor id,
writes the latter to `aux3`, and metadata decoding rejects unknown ids or a
descriptor whose size disagrees with the fixed count. Typed projection also
checks the selected static `AbiKind`, preventing same-width object/scalar
reinterpretation. Both immutable tables live in the refinement witness and
are preserved exactly across allocation extensions. The local decoder,
allocation, prefix, and closure-cell transport proofs have been strengthened
to use the descriptor table; the next slice consumes it in executable
ownership traversal.

W6.4i consumes the table in executable ownership traversal. The reusable
capture address, typed slot decoder, and descriptor lookup now live below the
ownership runtime rather than behind `ClosureRuntime`. `readOwnedReferences`
recovers the exact `aux3` descriptor, checks its fixed-count agreement, skips
scalar lanes, and returns object-representation words in source order.
Descriptor metadata is threaded unchanged through recursive decrement,
multi-decrement, and reset. An executable regression allocates a closure with
one heap constructor and one `UInt64` capture, observes only the constructor
as owned, then verifies that releasing the closure recursively frees both
allocations. The next slice proves this filtered decoder corresponds to FIR's
closure-owned-value fold and lifts the release into the heap relation.

W6.4j proves the filtered ownership decoder boundary. `closureOwnedValues`
selects exactly the semantic captures whose static ABI kinds carry object
words; a list induction shows `readClosureOwnedReferences` returns those
words in source order under `OwnershipValuesRel`, while typed scalar captures
are skipped. `ClosureObjectRel` supplies every pointwise typed read, and the
stronger `ClosureCellRel` packages the exact live header, descriptor lookup,
ordinary flag, and fixed count needed to lift that result through the public
`readOwnedReferences`. The next slice constructs this complete cell relation
after allocation and embeds it in `LiveCellRel`.

W6.4k constructs that complete cell relation after allocation. The local
allocation theorem now retains its exact live header and semantic capture
extent instead of discarding them after proving `ClosureObjectRel`.
`ClosureObjectRel.freshCellRel` checks that the caller's dispatch and
descriptor tables are exactly the module tables, then packages the canonical
fresh semantic closure cell with reference count one, ordinary persistence,
and live status. `allocateClosure_cellRel` exposes the resulting frontier and
cell relation as one public vertical postcondition. The next slice can add a
single `LiveCellRel.closure` constructor backed by this package.

W6.4l adds that structural closure case. `LiveCellRel` is exhaustive over
constructors, closures, boxed scalars, promoted tags, and naturals; closure
allocation now extends the whole live heap, and all generic prefix, witness,
reference-count, and reset/reuse frames preserve the new case. This removes
the former proof boundary where closures had a local decoder theorem but no
place in the global heap invariant.

W6.4m closes descriptor-aware closure release. A count-one closure first
marks its parent allocation dead, then recursively releases exactly the
object-like captures selected by its static descriptor, in source order.
Scalar and reuse-token captures are proved semantic ownership no-ops rather
than being silently reinterpreted as object words. Public decrement and reset
thread the immutable descriptor table through their complete-heap refinement
proofs. The former standalone closure reference-count module is consolidated
into the common reference-count correctness layer.

W6.4n begins the generated-runtime boundary with mutable globals. Static
declarations allocate typed slots whose companion initialization flags start
clear; checked reads distinguish unknown, mismatched, and uninitialized
globals, while checked writes retain declaration order and frame every other
slot. A bidirectional pointwise relation proves initial empty-cache
refinement, semantic `setGlobal` preservation, and successful typed reads.
`ConcreteRuntimeRel` layers this table plus world and external trace over the
existing `LiveHeapRel`, so later W6.5 effects can reuse the heap proofs rather
than duplicating them. The next checkpoint adds the external request/response
contract and structured effect/fault correspondence.

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

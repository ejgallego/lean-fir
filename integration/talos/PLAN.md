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
| 2026-07-20 | A0 final-twelve closure | proof, concrete-runtime, and integration owners | ready | The generated `tuple-rotate` fast reset path now carries an exact symbolic object refinement: the support gate requires `isShared(candidate) == 0`, ties the fact to the same `tobject` jump argument, and proves all live uses remain in that false arm. A mismatched-guard fixture fails closed. The symbolic validator checks the refined read, while binary encoding and the Talos adapter retain the same physical `local.get`; `AbiKind.refines` and the semantic runtime ABI are unchanged. Together with scalar-case, guarded-join, and erased-delete slices, all original final twelve cases now pass in the default native↔V8 matrix, which covers 52 compiler-produced cases including the shared-delete companion. No new runtime import or proof-lane semantic duplication was introduced. |
| 2026-07-20 | A0 complete-corpus pure expansion | generation and integration owners | ready | The already-supported `lit-nat`, `id-nat`, `pair-first`, `local-tail`, and `big-ctor-70` programs now run in the default native↔V8 matrix. They cover closed and parameterized naturals, object projection, compiler-generated local tail recursion, and a seventy-field constructor projection without changing `WasmSupported`, the runtime import vocabulary, or any shared semantic contract. The default matrix grows from 52 to 57 compiler-produced cases; controlled effects and exact large-`Nat` transport remain the seven explicit corpus-closure follow-ups. |
| 2026-07-20 | A0 controlled V8 effects | generation and integration owners | ready | The V8 semantic host now retains a private immutable before/after heap view for each successful external call while leaving its public runtime trace unchanged. The validation adapter projects only corpus-declared externals through their argument/result schemas, preserving call order and event-time values. `effect-record-nat`, `effect-record-twice`, and the twice-mutated `effect-record-byte-array-twice` case pass native↔V8; the latter distinguishes original, intermediate, and final bytes even though all values use one heap location. Exact validation-owned external handlers advance the world in lockstep with the LCNF model. The default matrix grows from 57 to 60 compiler-produced cases without weakening `WasmSupported` or changing a shared observation contract. |
| 2026-07-20 | A0 exact-Nat corpus closure | generation and integration owners | ready | Validation protocol v2 changes only the wire representation of arbitrary semantic `Nat` datums: `nat.value` is now a canonical decimal string, decoded back to Lean `Nat` with malformed and noncanonical inputs rejected. Python, native Lean, LCNF, product manifests, plans, and the V8 runner move together. `large-nat`, `nat-list-roundtrip`, `nat-add-tagged-to-heap`, and `nat-add-heap-input` close the default native↔V8 matrix at all 64 compiler-produced corpus cases. This is an isolated shared validation-wire-contract commit; runtime step semantics, observations after decoding, the semantic Wasm ABI, `WasmSupported`, and runtime imports are unchanged. `FIR-BUG-wasm-none-json-nat-precision` is fixed. |
| 2026-07-20 | A0 `Std.Format.prettyM` execution | generation and integration owners | ready | A locally expanded monomorphic facade now generates and executes Lean 4.32's standard pretty printer in V8 through the raw `Format(tobject) × Nat(tobject)^3 → String(object)` semantic ABI. Recursive source-helper internalization leaves 20 declaration-level runtime primitives; ordinary format heap graphs are passed directly, and native `Std.Format.pretty` agrees on both the nested-line example and an all-constructor Unicode/newline case. `FIR-BUG-wasm-none-pretty-state-refinement` records the remaining generic final-LCNF provenance gap; `FIR-BUG-wasm-none-erased-closure-projection` and `FIR-BUG-wasm-none-lcnf-capture-environment-pollution` fix two adapter defects; `FIR-BUG-wasm-none-scalar-projection-index-naming` records the shared runtime naming trap exposed by the raw heap fixture. No shared semantic contract or proof-owned file changed. |
| 2026-07-21 | A0 reusable `prettyM` client | integration, proof, and concrete-runtime owners | ready | `call-pretty-format.mjs` starts with an empty semantic heap, instantiates the artifact once, and repeatedly passes caller-allocated raw Lean `Format` handles. `FIR-BUG-impure-none-cached-heap-persistence` is fixed by shared commit `bf9b9da` and Wasm commit `df6873d`: the FIR interpreter, JavaScript host, and concrete runtime recursively mark cached graphs persistent before publication. The original standalone group now renders at widths 80 and 5, nested-root/child header regressions pass, and W6 exposes the remaining constructive heap proof as `CachePersistenceRefines` instead of assuming the heap is unchanged. |
| 2026-07-21 | W3 exported-entry differential boundary | integration owner | ready | Correct cache persistence exposed `FIR-BUG-wasm-none-export-entry-cache-mismatch`: the oracle entered nullary `main` through the internal declaration cache while Wasm entered the exported body directly. Commit `9067434` binds export parameters and starts the source code body, matching the established W4 proof boundary. All heap-returning artifact fixtures and the complete deterministic Talos artifact audit pass. No FIR runtime or generated cache contract changed. |
| 2026-07-21 | A0 module-only artifacts | generation and integration owners | ready | `ModuleArtifact.moduleManifest` and `ModuleArtifact.write` emit the already-checked Wasm module with an invocation-free descriptor containing only source/export identity, raw parameter/result ABI, and exact semantic-host imports. `#fir_wasm_emit_module` exposes that path for ordinary declarations; both `idUSize` and the special `prettyM` compiler path produce byte- and LCNF-identical module-only/invocation-bearing outputs. The reusable JavaScript Format client now consumes only the module descriptor and constructs all runtime values itself. Invocation manifests and the semantic ABI are unchanged. |
| 2026-07-21 | A0 browser-compatible semantic host | generation and integration owners | ready | The semantic host and validation/Format external registries now use a platform-neutral assertion module rather than Node built-ins. A Fetch-only module Web Worker loads the invocation-free compiler-produced `prettyM` module and its descriptor, then runs the same raw Lean 4.32 `Format` layouts, Unicode coverage, repeated calls, and cache-persistence regression as the Node client in headless Chrome 150.0.7871.114. The browser check is opt-in so Chrome is not required tooling; no semantic ABI, proof-owned file, or concrete-runtime contract changed. |
| 2026-07-22 | A0 shared-product browser corpus | generation and integration owners | ready | The Node V8 adapter now delegates descriptor validation, ABI encoding, Wasm import/export checks, result normalization, and effect projection to one browser-neutral executor. A Fetch-only module Worker consumes the validation harness's exact `lean-wasm-semantic` bundle, verifies every case-bound manifest/module digest with Web Crypto, executes all 64 compiler-produced cases in Chrome, and matches each observation against the canonical Node/V8 result from the same matrix. The browser remains opt-in; no semantic ABI, observation contract, proof-owned file, or concrete-runtime contract changed. |
| 2026-07-22 | A0 concrete-switch readiness | generation, concrete-runtime, proof, and integration owners | ready | A deterministic fail-closed report now checks the emitter's complete fixture inventory, concrete import construction, initial-runtime loading, external implementations, and every module-local import site's current W6 coverage. All 44 emitted artifacts are classified and concrete-resolvable: 43 match the live FIR oracle, including the formerly omitted `reference-counting` and `delete-fault`, while `mutation` retains its exact expected layout fault. Ten of 13 compiler-produced source probes preflight successfully; the three `prettyM` forms expose the same 20 missing concrete externals, and the coverage form additionally exposes packed initial constructors. The report explicitly does not claim proof completion or concrete source/product execution. No shared semantic contract or proof-owned file changed. |
| 2026-07-22 | A0 concrete Format Nat/String externals | concrete-runtime, proof, and integration owners | ready | The external-engine concrete registry now implements the five `Nat`, eight UTF-8/string, and two unreachable-fallback declarations retained by compiler-produced `prettyM`. Heap arguments are resolved back to checked physical addresses and read through the existing natural/string layouts; results use the existing concrete allocators, while the browser-safe semantic and concrete paths share one pure UTF-8 algorithm module. Focused regressions cover promoted and heap naturals, Unicode byte/code-point navigation, fresh results, stale and wrong-kind inputs, unchanged world, exact trace order, and structured fallback traps. Readiness now reports only the five `Int` declarations, plus the coverage fixture's independent packed-initial-constructor gate. Heap-`Int` layout and packed placement remain W6-owned contracts; no proof-owned file or shared semantic ABI changed. |
| 2026-07-23 | A0 concrete Format Int externals and `prettyM` execution | generation and concrete-runtime owners | ready | The concrete host now consumes W6's landed sign-magnitude heap-`Int` layout while retaining signed 32-bit tagged immediates, and the registry implements `Int.add`, `Int.sub`, `Int.decLt`, `Int.natAbs`, and `Int.ofNat` with exact `BigInt` semantics. A reusable Node/browser checker allocates only raw Lean 4.32 `Format` layouts, calls the invocation-free compiler-produced `prettyM` export through its physical ABI, and decodes the concrete Lean string result; no high-level format adapter is introduced. Readiness advances to 12/13 source probes, leaving only packed initial-constructor loading for the coverage invocation. Focused boundary, wrong-kind, stale-object, trace, Node, and browser regressions are wired into the lane gates. No proof-owned file or shared semantic contract changed. |
| 2026-07-23 | A0 packed initial constructors and source readiness closure | generation and concrete-runtime owners | ready | The concrete manifest loader now consumes packed constructor scalar fields using W6's existing physical layout: it requires the compiler-shaped `size + usize` coordinate, checks width-specific unsigned values and `UInt32` extent, rejects incoherent overlapping bytes, derives the minimal `ssize`, and writes `UInt8`/`UInt16`/`UInt32`/`UInt64` little-endian after fixed slots. Descriptor-backed observation round-trips the exact manifest fields. The formerly blocked all-constructor `prettyM` invocation now loads its 23-cell `Format` graph and returns the native-oracle Unicode/newline string in Node and the browser. Concrete-switch readiness reaches 13/13 source probes and 44/44 artifact fixtures; W6 proof coverage remains reported separately and incomplete. No proof-owned file or shared semantic contract changed. |
| 2026-07-23 | A0 complete concrete source execution inventory | generation and concrete-runtime owners | ready | One browser-neutral checker now owns frozen low-level ABI expectations for all 13 compiler-produced source artifacts and fails closed if the declared inventory drifts. Node and the browser execute all 11 invocation manifests and both invocation-free modules, round-trip every manifest argument and initial heap cell, and compare scalar, `USize`, `Nat`, Unicode string, and raw-layout `prettyM` results. This replaces duplicated Nat/string/pretty environment checks and closes the readiness audit's source-execution disclaimer without adding a JavaScript facade. No proof-owned file or shared semantic contract changed. |
| 2026-07-23 | A0 concrete shared-product execution | generation and concrete-runtime owners | ready | A browser-neutral concrete validation adapter consumes the validation harness's exact `lean-wasm-semantic` product bundle, rechecks each compiler manifest and physical import/export ABI, executes every case whose initial heap is represented, and compares schema-normalized results and controlled Nat effects with the canonical V8 observation. Node and Chrome execute 65/95 products through concrete wasm32 memory. The exact remaining 30 IDs fail closed at one frozen boundary: each contains an initial `ByteArray`, and some also require its external family. `Int.neg` and the Nat recording external are covered without weakening that gate. No proof-owned file or shared semantic contract changed. |
| 2026-07-23 | W7 optional resident-memory surface | generation, proof, and integration owners | ready | The symbolic module, validator, binary encoder, and Talos adapter now carry an optional defined/exported wasm32 memory plus the checked `i32.and`, `i32.shr_u`, `i32.load`, `i64.load`, and `i32.wrap_i64` operations needed by the first resident `getTag` helper. Memory is absent by default, so every existing semantic/concrete-host artifact remains byte-identical; the compiler-produced `prettyM` digest stays `fc193be200ff7fabdb6f7edc92242a4df047a0db7f1436aeb6d7b263d5fe3767`. This standalone surface commit adds no resident helper and changes no W6 layout/runtime contract or proof theorem. Proof work need only rebase before consuming later W7 helper definitions. |
| 2026-07-24 | W7 resident `getTag` artifact | generation and integration owners | ready | A deterministic 236-byte standalone module now exports its own one-page memory and raw `fir_getTag : tobject → UInt32` helper with zero imports. The helper consumes W6's current word classification, 32-byte header offsets, object-kind codes, liveness/persistence flags, and promoted-tag marker directly. One browser-neutral client passes immediate, live-constructor, and promoted-tag results and checks zero, misaligned, and dead-object traps in Node and Chrome without JavaScript runtime handlers. Talos accepts the complete helper module. This is generation readiness only: W6 still owns the later theorem relating successful helper execution to its `getTag` contract, and no W6 definition or proof file changed. |
| 2026-07-24 | W7 shared module-memory host boundary | generation and integration owners | ready | `ConcreteHost.attachMemory` moves a manifest-prepared concrete heap into a zero-initialized module-exported `WebAssembly.Memory`, rejects dirty memory and rebinding, and routes later allocation and growth through that same memory. The resident `getTag` client checks constructors and promoted tags allocated both before and after attachment and grows the heap past one page in Node and Chrome. Existing no-memory modules retain the private-buffer path unchanged. This removes the dual-heap hazard before compiler-produced `prettyM` starts internalizing imports; no Wasm ABI, W6 definition, or proof claim changed. |
| 2026-07-24 | W7 compiler `prettyM` resident-`getTag` link | generation and integration owners | ready | A checked post-lowering linker rewrites every semantic `getTag` call in the compiler-produced `prettyM` module to the Wasm-resident `fir_getTag`, rebuilds canonical runtime imports, rejects declaration or memory collisions, and preserves the captured final LCNF byte-for-byte. The resulting module defines/exports its one-page memory and helper, and moves from 351 to 350 function imports with no memory import. The same raw Lean 4.32 `Format` layouts and native-oracle strings pass in Node and Chrome after the generic module client attaches the concrete host to exported memory. This is the first incremental runtime-closure reduction, not the final zero-import W7 acceptance or the W6 helper-correctness theorem; no W6 definition, proof-owned file, or shared semantic contract changed. |
| 2026-07-24 | W7 resident `isShared` and compiler link | generation and integration owners | ready | A deterministic 209-byte standalone module now defines one-page memory and exports import-free `fir_isShared : tobject → UInt8`. Direct Node/Chrome checks cover immediate, unique, non-unique, persistent, promoted-tag, zero, misaligned, and dead-object paths against W6's current live/persistent/refcount header layout. The generalized checked linker then internalizes `isShared` after `getTag` in compiler-produced `prettyM`, preserves final LCNF byte-for-byte, and reduces function imports monotonically from 351 to 350 to 349. Both retained incremental artifacts execute the same raw Lean 4.32 `Format` layouts and native-oracle strings through module-owned memory. This remains generation readiness, not the resident-helper contract theorem; no W6 definition, proof-owned file, or shared semantic contract changed. |
| 2026-07-24 | W7 narrow byte-load surface | generation, proof, and integration owners | ready | The symbolic instruction set, stack validator, binary encoder, and Talos adapter now carry typed `i32.load8_u`, encoded with its canonical zero alignment and adapted to Talos's existing `load8U`. The resident-memory surface module exercises the instruction as `UInt8` beside the prior bit/word/64-bit-load cases, while modules that do not select it remain unchanged. This isolated compatibility surface prepares packed `UInt8` projection internalization; it adds no runtime helper, changes no semantic Wasm ABI or W6 contract, and makes no projection-correctness claim. |
| 2026-07-24 | W7 resident prettyM read projections | generation and integration owners | ready | A deterministic 983-byte standalone module defines/exports one-page memory, has zero imports, and exports the exact four object-slot plus four packed-`UInt8` projection descriptors reachable from Lean 4.32 `prettyM`. Raw-header and concrete-host Node/Chrome checks exercise every helper and the recognized invalid heap guards without JavaScript runtime handlers; Talos accepts the complete module. The checked post-lowering link preserves final LCNF byte-for-byte and advances compiler `prettyM` from 349 to 341 function imports, retaining earlier artifacts for the 351 → 350 → 349 → 341 audit. `FIR-BUG-wasm-none-value-producing-if-encoding` also repaired the validator/encoder invariant by rejecting stack-changing arms for the encoder's empty-block `if`; helpers use typed locals across their guards. Projection bounds and packed-coordinate correctness still rely on W6 related-state preconditions and remain proof-lane obligations; no W6 definition, proof-owned file, or shared semantic contract changed. |
| 2026-07-24 | W7 resident prettyM closure projections | generation and integration owners | ready | A deterministic 1,466-byte standalone module defines/exports one-page memory, has zero imports, and exports twelve typed physical capture readers covering all 87 `closureProj` operations reachable from compiler-produced `prettyM`. Helpers are shared by slot/result kind while compiler call sites retain their full function/arity/fixed descriptor. Raw-header and concrete-host Node/Chrome checks cover every helper plus recognized invalid heap guards; Talos accepts the module. The checked link preserves final LCNF, removes all 87 closure-projection imports, and advances the retained audit to 351 → 350 → 349 → 341 → 254. Operation-specific metadata, bounds, and capture-kind correctness remain W6 related-state proof obligations; no W6 definition, proof-owned file, or shared semantic contract changed. |
| 2026-07-24 | W7 stable closure-dispatch contract | generation, proof, and integration owners | ready | Closure target IDs are now explicit module metadata instead of being reconstructed from the surviving runtime-import order. Lowering records a duplicate-free first-use `closureDispatch`; validation requires every imported closure target to be present; all module and invocation manifests expose the table; resident linking preserves it; and the concrete host consumes it when allocating closures. A regression covers a match-only target preceding an allocatable target, the exact case that would otherwise renumber later headers after match internalization. This is an isolated shared semantic-Wasm-ABI contract commit: W6's `RefinementWitness.closureDispatch` must relate to this same table, and both feature lanes rebase before dependent work. |
| 2026-07-24 | W7 resident prettyM closure matches | generation and integration owners | ready | A deterministic 635-byte standalone module defines/exports one-page memory, has zero imports, and tests true target matches plus independent target-ID, arity, and fixed-count mismatches against raw and concrete-host closure headers. Recognized zero, immediate, misaligned, dead, and non-closure inputs trap without JavaScript handlers; Talos accepts the complete module. The checked linker emits exact helpers for all 77 `closureMatches` operations using the retained 38-target dispatch table, preserves final LCNF, and advances compiler `prettyM` from 254 to 177 function imports while the raw Format corpus continues to match the native oracle. This is generation readiness only; descriptor/table validity and the theorem relating physical header comparisons to W6 semantic `closureMatches` remain proof-lane obligations. |
| 2026-07-24 | W7 initialized resident-global contract | generation, proof, and integration owners | ready | The symbolic module now carries typed initialized mutable resident globals after the existing lazy-cache flag/value prefix. Validation checks initializer/value-type agreement and resolves `global.get`/`global.set` through the combined stable order; the binary encoder retains integer values and floating-point bit patterns; and the Talos adapter constructs the same initial global store. A deterministic 95-byte zero-import module observes the nonzero `1024` initializer and a later mutation in Node and Chrome. This is an isolated shared semantic-Wasm-ABI contract commit needed by the resident heap frontier: both feature lanes rebase before allocator-dependent work, while W6's `MemoryState.heapCursor` remains unchanged and no proof theorem is claimed. |
| 2026-07-24 | W7 resident allocation instruction surface | generation, proof, and integration owners | ready | The checked symbolic instruction set, binary encoder, and Talos adapter now agree on physical `i32.add`, `i32.sub`, `i32.lt_u`, `i32.load16_u`, typed 8/16/32/64-bit stores, and `memory.size`/`memory.grow`. A deterministic 439-byte zero-import module owns one-page memory, exercises every new opcode through raw exports, grows to two pages, and passes identically in Node, Chrome, and Talos. Existing lowering never selects this additive surface, and this slice neither consumes the resident frontier global nor changes W6's heap/runtime relation. It is the final independent prerequisite before the standalone Wasm allocator. |
| 2026-07-26 | W7 resident constructor allocation and styled package | generation and integration owners | ready | A deterministic 1,015-byte standalone module owns/exports memory, has zero imports, and implements empty-immediate plus mixed-layout nonempty constructor allocation through the resident heap allocator. Its Node/Chrome/Talos checks cover exact headers, object and `USize` slots, packed bytes, zero padding, frontier motion, and scratch preservation without JavaScript runtime handlers. The checked linker removes all 23 constructor imports from text `prettyM`, advancing the retained audit from 177 to 154 while preserving final LCNF; the styled facade removes 27 and packages atomically at 157 imports with exact native-oracle tag events. Two adapter regressions record and fix the temporary mixed host/resident frontier invariant and raw decoding of Wasm-born results. This is generation readiness only: W6 still owns the theorem relating resident allocation to its semantic contract, and no W6 definition or proof-owned file changed. |
| 2026-07-27 | W7 stable closure-descriptor contract | generation, proof, and integration owners | ready | Closure capture-layout IDs are now explicit retained module metadata instead of being reconstructed from surviving `partialApply` imports. Lowering records a duplicate-free first-use `closureDescriptors` table; validation requires every imported `partialApply` descriptor to be present; module/invocation manifests expose it; resident linking preserves it; and both the executable concrete host and Talos resolver consume the retained table. The compiler-produced `prettyM` module freezes 14 descriptor rows, including the zero-capture row, and a regression proves that an unrelated earlier descriptor keeps the allocated header ID stable. This isolated shared semantic-Wasm-ABI contract is the prerequisite for eliminating all 87 `partialApply` imports: W6's `RefinementWitness.closureDescriptors` must relate to the same table, and both feature lanes rebase before dependent work. |
| 2026-07-27 | W7 resident literal allocation and immediate-Natural link | generation and integration owners | ready | A deterministic 1,375-byte standalone module owns/exports memory, has zero imports, and implements immediate Naturals plus empty and Unicode/newline UTF-8 String allocation through the resident allocator. Raw-header and `ConcreteHost` checks freeze the current W6 String marker, byte count, payload, padding, frontier, and scratch behavior. The accepted mixed-runtime linker internalizes only the two text and four styled immediate-Natural imports, advancing text `prettyM` from 154 to 152 and the exact-event facade from 157 to 153 while preserving final LCNF and retained closure tables. `FIR-BUG-wasm-none-resident-import-location-registry` records why the already-tested String helper waits for its JavaScript-consuming externals to become resident instead of guessing host allocation identities. This is generation readiness only; no W6 definition, proof-owned file, or shared contract changed. |
| 2026-07-27 | W7 resident closure allocation and `partialApply` link | generation and integration owners | ready | A deterministic 1,253-byte standalone module owns/exports memory, has zero imports, and allocates zero-capture plus mixed `tobject`/`UInt8`/`USize` closures through the resident frontier. Raw-header and `ConcreteHost` checks freeze W6's 32-byte closure header, eight-byte capture slots, scratch preservation, and deliberately shifted stable target/descriptor IDs. The checked linker internalizes all 87 `partialApply` operations in both facades, preserves final LCNF and retained closure tables, and advances text `prettyM` from 152 to 65 function imports and the exact-event facade from 153 to 66. Current `prettyM` captures are all i32; unsupported float captures fail closed. This is generation readiness only: W6 remains independently responsible for proving the emitted helpers satisfy its closure-allocation contracts, and no proof-owned file or shared contract changed. |
| 2026-07-27 | W7 resident constructor setters | generation and integration owners | ready | A deterministic 486-byte standalone module owns/exports memory, has zero imports, and performs guarded object-slot plus packed-`UInt8` writes against exact W6 constructor headers. Node, Chrome, `ConcreteHost`, and Talos checks cover successful projection plus zero, misaligned, dead, out-of-bounds, and width-mismatched traps. The checked linker internalizes seven `objectSet` and four `scalarSet` operations in text `prettyM`, advancing it from 65 to 54 imports, and all ten styled setters, advancing exact-event `prettyM` from 66 to 56, while preserving final LCNF and retained closure tables. Ownership remains explicit in the adjacent LCNF `inc`/`dec` operations. This is generation readiness only; no W6 definition, proof-owned file, or shared contract changed. |
| 2026-07-27 | W7 resident nonrecursive increments | generation and integration owners | ready | A deterministic 511-byte standalone module owns/exports memory, has zero imports, and implements overflow-checked nonrecursive reference-count increments against exact W6 headers. Node, Chrome, `ConcreteHost`, and Talos checks cover checked immediate/promoted-tag no-ops, persistent no-ops, ordinary live-heap updates, invalid/dead address traps, unchecked-tag traps, and overflow. The checked linker internalizes all four `inc` operations in each facade, advancing text `prettyM` from 54 to 50 imports and exact-event `prettyM` from 56 to 52 while preserving final LCNF and retained closure tables. Recursive `dec`/`delete` remain a separate ownership-walk slice. This is generation readiness only; no W6 definition, proof-owned file, or shared contract changed. |
| 2026-07-28 | W7 resident recursive release and delete | generation and integration owners | ready | A deterministic 1,698-byte standalone module owns/exports memory, has zero imports, and implements count-one recursive release plus nonrecursive delete against W6's retained headers and closure-descriptor table. Parent-first canonical release handles constructor children and statically object-like closure captures; Node, Chrome, and `ConcreteHost` regressions cover checked immediate no-ops, ordinary and persistent counts, shared children, delete without recursion, stale/misaligned/underflow traps, descriptor rejection, and cycle-safe dead-header traps. The checked linker removes the five distinct `dec` operations plus `delete` from both facades, advancing text `prettyM` from 50 to 44 imports and exact-event `prettyM` from 52 to 46 while preserving final LCNF and both closure tables. The helper deliberately traps above a 32-constructor-object-field generation bound; current compiler-produced `prettyM` reaches at most five. This is generation readiness only; W6 still owns the theorem relating linked helpers to its recursive-release contract, and no W6 definition, proof-owned file, or shared contract changed. |
| 2026-07-28 | W7 resident styled constructor-tag mutation | generation and integration owners | ready | A deterministic 230-byte standalone module owns/exports memory, has zero imports, and performs one fixed constructor-tag write after validating the exact aligned live-constructor boundary. Node, Chrome, and `ConcreteHost` checks cover isolated `aux0` mutation, scratch restoration, successful independent tag decoding, and zero, misaligned, dead, and non-constructor traps; tags outside the `UInt32` header lane fail generation. Plain-text `prettyM` has no `setTag` operation and remains at 44 imports. The exact-event facade's single `setTag 1` operation is now resident, advancing the styled package from 46 to 45 imports while preserving final LCNF and both closure tables. This is generation readiness only; W6 still owns the helper-refinement theorem, and no W6 definition, proof-owned file, or shared contract changed. |

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
semantics remain explicit coordinated follow-ups. The large-`Nat` JSON
protocol boundary is now exact under protocol v2.

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

The exact program-level proof obligations and the W7 linking boundary are
tracked in [`W6-THEOREM-ROADMAP.md`](W6-THEOREM-ROADMAP.md). The operation
inventory below is necessary evidence for those theorems, but operation
coverage alone is not the W6 completion criterion.

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

W6.5a establishes the successful external-call boundary. Concrete requests
retain exact source types alongside typed physical arguments; concrete
responses carry the returned lane, updated linear memory, and world. The host
contract permits allocation and mutation only when it supplies an extended
witness, a complete post-call `LiveHeapRel`, and a result related at the
declared ABI kind. From those obligations, `ConcreteRuntimeRel` proves the
exact source `resumeExternal` runtime: generated globals are preserved, world
is replaced by the response, one related event is appended to the trace, and
the result lane refines the semantic value. The next W6.5 slice freezes the
source/target fault encoding and proves failing host calls cannot masquerade
as successful effects.

W6.5b freezes that fault boundary. `ConcreteError.toTrap` is a lossless,
injective classification into source-origin failures and backend-only target
failures; memory and generated-global faults remain distinct target payloads.
Address-indexed source failures are related back to exact FIR runtime faults
through `HeapReferenceRel`, so a physical reference-count underflow denotes
the corresponding semantic location rather than leaking a Wasm address into
source observations. A failed concrete external invocation returns no
post-state at all, and the exact source-failure theorem agrees with the
semantic `ExternalImpl` error. The next slice audits the remaining successful
operation/fault matrix before W6.6 composition.

That audit found and closed a latent W6.4 whole-heap gap as W6.4o. Closure
allocation previously established exact bytes, metadata, captures, a fresh
`ClosureCellRel`, and a prefix frame, but stopped short of assembling the new
cell into `LiveHeapRel`. `allocateClosure_liveHeapRel` now extends the semantic
heap and proof witness together, preserves every old cell and promoted tag,
adds the descriptor region, and relates the returned closure as both `object`
and `tobject`. `LiveHeapRel.initial` and `ConcreteRuntimeRel.moduleInitial`
also provide the missing generated-module entry state with frozen closure
tables and declared-but-uninitialized globals. The next audit slice lifts the
remaining successful single-cell mutations from local decoder relations to
the complete heap/runtime boundary required by W6.6.

W6.5c begins that complete-heap mutation lift with constructor tags.
`writeTag_header` exposes the exact extent-preserving common-header
transaction behind a successful checked update. `LiveHeapRel.writeTag_refines`
then combines the existing local constructor decoder theorem with the generic
descriptor-disjoint header frame, performs the matching semantic `setTag`,
and reconstructs every target and non-target cell without changing the ghost
witness. Payload-backed `USize` and packed-scalar writes are the next audit
slice; they need the analogous write-region frame rather than the common
header frame used here.

W6.5d establishes that payload-write boundary and applies it to `USize`
mutation. `TargetMutationFrame` records an unchanged target header, stable
memory size/frontier, and complete byte frames for every allocation disjoint
from the target's retained extent. Its generic whole-heap theorem preserves
descriptor regions, pairwise disjointness, non-target semantic cells, and
promoted tags while replacing exactly one source cell. A successful checked
64-bit `USize` store now supplies that frame, performs the matching semantic
`setUSizeField`, and yields a complete `LiveHeapRel`. Packed scalar widths can
reuse the same boundary by supplying their width-specific byte transaction.

W6.5e consumes the shared erased-delete correction from `fc6d3e4`. Concrete
`deleteObject` now recognizes physical word zero as the operation-specific
failed-reset sentinel and returns the complete memory state unchanged;
`LiveHeapRel.deleteObject_erased_refines` pairs that equation with semantic
`deleteValue_erased`. The ordinary heap deletion proof explicitly establishes
that its decoded address is nonzero before entering the header path, and the
existing immediate/promoted rejection regression remains intact. Thus this
slice does not widen `ValueRel`, heap-only ABI decoding, or ordinary object
classification.

W6.5f applies the generic payload frame to the first packed scalar lane.
Successful checked `UInt64` mutation is now bounded by the constructor's
static descriptor, preserves the frontier and every disjoint allocation,
performs semantic `setScalarField`, and reconstructs the complete
`LiveHeapRel`. Scalar-capacity premises remain at the ABI descriptor boundary
rather than being duplicated in semantic `ConstructorObject`; the remaining
32-, 16-, and 8-bit lanes can use the same assembly with their width-specific
checked writes.

W6.5g extends that complete-heap result to packed `UInt32`. The checked
four-byte writer now supplies the same target-header, disjoint-allocation, and
frontier frame as the 64-bit lane; semantic `setScalarField` and the concrete
decoder relation are rebuilt at the unchanged static descriptor. The
remaining mutation audit is reduced to the two narrow byte writers (`UInt16`
and `UInt8`).

W6.5h closes that narrow mutation matrix. Checked `UInt16` and `UInt8`
transactions now preserve the target header, zero frontier, and every
descriptor-disjoint allocation through the same `TargetMutationFrame` used by
the wider lanes. Their whole-heap theorems perform the corresponding semantic
`setScalarField` and rebuild `LiveHeapRel`. Constructor tag, `USize`, and all
four packed scalar widths therefore have complete successful-operation
refinements; the next audit checks the remaining runtime operation and fault
coverage before W6.6 composition.

The first W6.5 audit pass found four immediately actionable gaps in the
already-implemented object-operation subset: ordinary heap increment stopped
at `LiveCellRel`, one-field object mutation had no concrete operation, packed-
scalar reads stopped at the constructor decoder, and closure match/capture
projection stopped at the local closure relation. The subsequent full
`RuntimeOp` audit is maintained in `integration/talos/W6-COVERAGE.md`; it also
tracks literals, closure application, tagged operation wrappers, failures,
W6.6 composition, and artifact switching. Structured failure correspondence
is currently complete for external calls and selected ownership paths, but
not yet for the full matrix.

W6.5i closes the first audit gap. A successful ordinary heap increment now
exposes its exact extent-preserving header write, performs FIR's matching
`incValue`/`setCell` transition, and uses the shared header-frame assembler to
preserve every other live, dead, and promoted allocation under `LiveHeapRel`.
The existing tagged-value equation retains both checked no-op and unchecked
source-fault behavior. One-field object mutation is the next successful
operation slice.

W6.5j adds that missing `.objectSet` operation. `writeObjectField` validates
the constructor, bounds, and existing canonical high-word padding before
replacing only the low wasm32 word of the eight-byte semantic slot. Its local
proof reads back the new typed `ValueRel`, frames every other object, `USize`,
and packed-scalar observation, and preserves the zero frontier. The complete
heap theorem widens the active-layout frame to any retained reuse capacity,
performs FIR's matching `setObjectField`, and reconstructs `LiveHeapRel` for
all non-target allocations. Packed-scalar and closure projections remain the
successful-operation audit gaps before the full structured-fault matrix.

W6.5k closes integer packed-scalar projection at the complete heap boundary.
A successful semantic `getScalarField` now exposes the exact selected field
and its compiler width/offset operands; the decoded constructor relation then
proves checked concrete `UInt8`, `UInt16`, `UInt32`, or `UInt64` readback and
the corresponding ABI-indexed `ValueRel`. Float projection remains outside
the claim under `FIR-BUG-wasm-none-float-runtime-gap`, because the shared FIR
runtime still has no semantic float scalar values. Closure match and capture
projection are the remaining successful read-operation audit gap.

W6.5l closes that closure read boundary. `ClosureObjectRel.matches_eq` now
proves the exact match/nonmatch `UInt32` result rather than only the positive
case. Mapped live closures lift that equation through `LiveHeapRel`, while a
descriptor-aligned capture projection returns the checked concrete lane and
its ABI-indexed `ValueRel`. These theorems intentionally stop at the W2
`closureData` boundary owned by the Talos integration layer; W6.6 composition
will connect them without duplicating the semantic host contract in
`Fir/Wasm/Concrete`.

W6.5m closes natural literals across the immediate/heap representation
boundary. The formerly opaque recursive limb splitter is now total and
well-founded; its canonical base-`2^64` value equation, bounded payload
writer, header/frontier frame, and decoder round trip are proved. Successful
large-natural allocation now extends `LiveHeapRel`, binds the fresh semantic
location and natural descriptor, and returns the corresponding `.tobject`
`ValueRel`; tagged naturals continue to use the existing immediate encoder.
An executable two-limb guard covers the nontrivial codec path. String
literals remain the unsupported literal case in the W6 coverage matrix.

W6.5n closes the empty-constructor representation branch. A successful
zero-field constructor allocation now exposes the exact semantic `allocCtor`
equation, preserves `LiveHeapRel`, and returns a precise `.tagged` `ValueRel`
whether the concrete encoder chooses an immediate word or a promoted-tag
allocation. Explicit conversions between exact tagged relations and the
representation-polymorphic `.tobject` boundary make that ABI refinement
visible rather than burying it in an existential witness.

W6.5o closes `.getTag` at its declared `.tobject` input boundary. The complete
wrapper now dispatches proof-side between mapped live constructors and exact
tagged references; the latter decodes identically for immediate words and
promoted-tag allocations. In both cases the concrete `UInt64` result is the
exact image of FIR's semantic `Nat` tag.

W6.6a establishes the first lowering-to-concrete-runtime composition slice.
`PhysicalValueRel` lifts W6's ABI-indexed concrete lanes into Talos values, and
the new concrete Talos host owns only `ConcreteRuntimeState` plus a structured
failure channel: it has no semantic handle table or source runtime to consult.
Its executable `getTag` import distinguishes arity, lane, and checked heap
failures. An exact host contract and host-polymorphic stack rules then compose
the actual generated `local.get; getTag; const; i32.eq; if` constructor-case
sequence with `ConcreteRuntimeRel` and the W5 compiler/adapter theorem. The
semantic-host artifact remains unchanged until the remaining supported
operations acquire the same boundary.

W6.6b generalizes that boundary to the first result-producing object read.
The executable `objectProj` host validates arity and lane shape, performs the
checked eight-byte-slot read, and returns the exact wasm32 field word. The
proof recovers the constructor descriptor and ABI-indexed result relation from
`ConcreteRuntimeRel`, writes that result to the compiler-assigned local, proves
the source interpreter's `oproj` step, and composes the actual generated
`local.get; objectProj; local.set` prefix with any already-composed
continuation. Witness-monotone physical-local lemmas introduced by this slice
are shared infrastructure for later allocation and mutation composition.

W6.6c carries the same read-and-bind proof through the first 64-bit physical
lane. The executable `usizeProj` host decodes an i32 object address, performs a
checked `USize` field read, and returns the full value in an i64 lane. Its
source-step, state/local refinement, compiler/adapter, and Talos continuation
theorems show that the W6.6 machinery is ABI-indexed rather than specific to
wasm32 object results. An executable maximum-`UInt64` fixture guards the
nontruncation boundary.

W6.6d completes composition for packed integer projections. One executable
dispatcher covers `UInt8`, `UInt16`, and `UInt32` i32 results plus the
`UInt64` i64 result; four operation-refinement lemmas connect those branches
to the existing complete-heap proofs, and one physical-value rule composes the
source `sproj`, generated read/call/write prefix, and continuation. A maximum
`UInt64` executable guard covers the wide lane. Float kinds produce a
structured unsupported-kind trap and remain governed by
`FIR-BUG-wasm-none-float-runtime-gap`.

W6.6e establishes the first allocation-producing composition rule. Natural
literals now execute directly against concrete memory for immediate,
promoted-tag, and limb-backed representations. Strengthened allocation
theorems return explicit monotone witness extensions, allowing the whole
runtime relation and every old global, trace entry, and local to survive heap
growth. The source literal step, generated host call/local write, and arbitrary
continuation compose under the resulting witness. Executable guards cover a
small immediate and a two-limb natural. String literals remain outside this
slice and are still an explicit coverage gap.

W6.6f composes constructor allocation across both physical representations.
The concrete Talos import decodes an arbitrary list of wasm32 object fields,
allocates directly in host-owned linear memory, and returns either the exact
tagged word for an empty constructor or the fresh heap address for a nonempty
one. Both heap refinements now expose monotone witness growth, and exact
`.tagged`/`.object` results widen to `.tobject` only through the ABI's declared
refinement. A host-polymorphic `local.get` sequence rule connects arbitrary
constructor arity to the source interpreter step, compiler/adapter output,
destination local, and continuation. Executable guards cover the immediate
empty case and a nonempty one-field allocation/readback. The generated
artifact still awaits the concrete-host switch.

W6.6g begins lazy-cache composition at the store boundary. A generic physical
lane decoder now covers every currently inhabitable ABI relation, and the
executable `cacheSet` host performs a typed `ConcreteGlobals` update while
returning the exact same Talos value. Its theorem lifts the existing whole-
runtime `setGlobal` refinement, while the generated suffix WP keeps the host
cache distinct from the Wasm value/flag globals and proves the exact
`cacheSet; global.set; i32.const 1; global.set` sequence. A maximum-`UInt64`
guard checks the wide lane. The remaining cache work is the interprocedural
lazy declaration call and surrounding hit/miss conditional; the artifact is
still pending.

W6.6h establishes the concrete partial-application allocation boundary. The
Talos host now carries immutable closure dispatch/descriptor tables, decodes
mixed-width captures without semantic handles, allocates the closure directly
in linear memory, and returns its heap address. The complete closure-heap
theorem exposes monotone witness growth, lifts the whole runtime relation, and
composes the arbitrary-arity host call plus destination-local write. A maximum
`UInt64` capture guard checks typed readback. Proof inspection also found that
`RuntimeOp.abiWellFormed` admits an impossible `.tagged` closure result; this is
recorded as `FIR-BUG-wasm-none-partial-apply-tagged-result`, and the refinement
claim remains restricted to exact `.object` or widened `.tobject`. The source
`pap`/compiler theorem and artifact switch remained follow-ups at that
checkpoint.

W6.6i completes partial-application composition through the source and
generated-code boundaries. A direct `pap` rule proves the interpreter's
strict-underapplication branch allocates the same semantic closure described
by the complete concrete heap refinement, then binds the returned physical
address under the grown representation witness. Its recursive `CodeWP` rule
connects the transparent compiler equation, Talos adapter output, arbitrary-
arity capture loads, exact host call, destination-local write, and an already-
composed continuation. Argument adaptation remains an explicit premise so the
rule supports every independently proved LCNF argument encoding rather than
assuming captures are all local variables. The generated artifact still uses
the semantic host; closure match/projection and trampoline/direct-call
composition remain the next proof slices.

W6.6j installs the two read-only concrete operations required by that
trampoline. `closureMatches` reads checked target/arity/fixed metadata and
returns the exact direct i32 discriminator, including the nonmatching zero
case. `closureProj` checks the same metadata and capture descriptor, then
returns the selected `i32`, `i64`, `f32`, or `f64` lane without semantic
handles. Complete-runtime refinements connect both hosts to the mapped live
semantic closure and preserve its typed capture relation; exact Talos rules
compose each generated `local.get; call` prefix with its operand-stack
continuation. An executable regression covers a successful match, a target
mismatch, and maximum-`UInt64` capture readback. The surrounding candidate
chain, underapplication/direct-call branch, source call execution, and
artifact switch remain open.

W6.6k composes the next generated control boundary without assuming which
candidate matches. A host-polymorphic Talos rule runs the concrete matcher,
consumes its direct i32 result in the generated zero-parameter/result `if`,
selects either the candidate body or remaining dispatch chain, and reconnects
both normal fallthrough and `break 0` to the surrounding instruction suffix
with the original operand tail. This rule is recursive-ready but deliberately
stops short of claiming the compiler's complete candidate fold: the selected
body still needs capture/argument assembly followed by concrete
underapplication or an interprocedural direct call.

W6.6l establishes the concrete interprocedural boundary used by both direct
LCNF calls and the saturated trampoline branch. `CallLetStepSimulates` now
tracks pre/post concrete runtimes, locals, and potentially grown
representation witnesses alongside the source interpreter's exact finite call
execution. Its recursive `CodeWP` rule connects that judgment to compiler and
adapter output. At the instruction level, a fuel-free store-specific Talos
`TerminatesWith` proof for an ordinary Wasm function composes with the exact
caller operand remainder and destination-local write. This keeps recursion in
ordinary Wasm calls and never reintroduces the excluded semantic
`closureApply` callback. Constructing the callee termination proof from a
concrete function-body `CodeWP`, and assembling the whole compiler candidate
fold, remain follow-ups.

W6.6m discharges the generic callee side of that boundary. A concrete-host
function postcondition implements Wasm's exact parameter consumption, result
truncation, caller-tail restoration, fallthrough, and explicit return cases.
The corresponding body theorem converts any proved function-body WP into
Talos's store-specific, fuel-free `TerminatesWith` predicate; a `CodeWP`
corollary supplies it directly from the W6 source/compiler/state judgment.
Together with W6.6l, a concrete callee proof can now feed a generated direct
call and destination-local write without semantic handles. The remaining
closure gap is structural assembly of all projected captures, new arguments,
candidate branches, and the compiler's complete fold; recursive callees must
still provide the usual well-founded family of body proofs.

W6.6n closes lazy caching's surrounding control and semantic judgment over the
concrete host. Host-polymorphic Talos rules now prove both populated-flag hits
and empty-flag misses, including zero-parameter/result block fallthrough and
the subsequent cached-value load. Witness-indexed `LazyLetStepSimulates` and
`LazyMissBodySimulates` judgments connect the interpreter's exact three-step
hit/four-step miss executions to target stores and locals; the recursive
`CodeWP` rule connects either path to compiler/adapter output and its
continuation. Together with W6.6g, the typed concrete `cacheSet` call and both
physical global writes are available inside the miss obligation. The
remaining cache work is to assemble the declaration call, concrete result
relation, cache suffix, and miss-block exit into one proof, then switch the
artifact host.

W6.6o closes that lazy-miss assembly. A tail-polymorphic, store-specific
`TerminatesWith` theorem for the zero-argument declaration now feeds the exact
generated `call; cacheSet; global.set; i32.const 1; global.set` miss body. The
proof reconnects normal block exit to the cached-value reload and destination
local write used by W6.6n. Small global-write frame lemmas derive, from the
generated value/flag indices being distinct, that the result remains readable
after the flag is populated; downstream proofs do not assume that store fact.
Together W6.6g, W6.6m, W6.6n, and this slice provide the complete compositional
lazy-cache proof boundary. Supplying each declaration body's concrete
termination/refinement proof and switching the emitted artifact to the
concrete host remain integration work.

W6.6p opens the no-result effect path and closes reference-count increment.
`EffectStepSimulates` and its recursive `CodeWP` rule retain the exact source
step, compiler/adapter witness, pre/post concrete state relation, and an
operand-tail-polymorphic target transformer; the reusable host rule composes
source-order local loads with a result-free exact-contract call. The concrete
increment host now covers ordinary heap objects and both immediate and
promoted tagged words, while persistent source increments use the compiler's
proved elision path. Exact `.object` and `.tagged` locals widen to the
`tobject` runtime input only through `AbiKind.refines`. Ordinary count growth
retains the existing checked wasm32 side condition
`cell.rc + amount < UInt32.size`; tagged values are checked no-ops and do not
consume it. Executable guards cover an ordinary header update and the
promoted-tag no-op. The same effect infrastructure is ready for mutation,
decrement, delete, reset, and reuse.

W6.6q instantiates that no-result path for constructor-tag mutation. The
concrete Talos host performs the checked header write and reports decoder or
range failures through the structured failure channel. Its local theorem lifts
the existing complete-heap `writeTag_refines` result to `ConcreteRuntimeRel`;
the composed theorem then joins the exact `.object` local, source evaluator,
real compiler and adapter, unary host contract, and continuation. Successful
semantic constructor updates are factored through a reusable heap-only frame
for the remaining object, `USize`, and packed-scalar mutations. The theorem
retains the exact `tag < UInt32.size` layout premise. An executable guard
changes a unary constructor's tag and rereads its original payload, confirming
that the concrete mutation touches only the header. Generated artifact
execution remains pending.

W6.6r composes one-field object mutation. A concrete binary Talos host accepts
the exact object and field wasm32 lanes, validates the live constructor, slot
bounds, and canonical padding, and replaces only the selected slot's low word.
The local refinement instantiates the existing complete-heap
`writeObjectField_refines` theorem and reuses the heap-only semantic frame from
W6.6q. A generic binary no-result effect rule then connects an FVar field
argument through the source evaluator, compiler, adapter, exact host contract,
and continuation. The proof retains the constructor descriptor, semantic index
bound, descriptor field-kind equality, and `AbiKind.isObjectField` fragment
premises; it does not reinterpret wider scalar lanes as object words. An
executable guard changes a unary constructor field from 23 to 47 and confirms
that its tag remains 8. Literal/non-FVar argument composition and generated
artifact execution remain pending.

W6.6s composes `USize`-field mutation through the same lane-polymorphic binary
effect rule. The concrete host takes a wasm32 constructor address and an exact
Lean64 i64 payload, checks the constructor and semantic `USize` index, and
updates only the selected eight-byte slot. Its refinement instantiates the
existing whole-heap `writeUSizeField_refines` theorem, while the composed rule
derives both physical locals from `StateRelated` and connects the source
evaluator, compiler, adapter, exact host contract, and continuation. The
semantic index bound stays explicit. An executable guard overwrites the
maximum `UInt64` fixture with 37, rereads all 64 bits, and confirms that the
constructor tag is unchanged. Generated artifact execution remains pending.

W6.6t composes the complete supported packed-integer mutation dispatcher.
`UInt8`, `UInt16`, and `UInt32` consume exact i32 lanes; `UInt64` consumes its
full i64 lane. Each branch selects the width-specific checked concrete writer,
instantiates its whole-heap refinement theorem, and joins the FVar source step,
compiler, adapter, binary host contract, and continuation. Descriptor identity,
the packed-slot equation, width-specific capacity, and the existing
`semantic.scalarFields = []` premise remain explicit. The last premise means
this slice proves first-field installation, not repeated or mutually disjoint
updates; closing that gap requires a byte-disjoint scalar frame theorem rather
than weakening the state relation. Executable guards cover all four maximum
integer values and the structured float-kind rejection. Float execution stays
tracked by `FIR-BUG-wasm-none-float-runtime-gap`; generated artifact execution
also remains pending.

W6.6u composes checked recursive reference-count decrement. The concrete
Talos host repeats the public checked release operation, using the frozen
closure descriptor table for typed captures; ordinary objects may decrement
in place or become dead and recursively release constructor fields, closure
captures, and boxed ownership, while immediate and promoted tags remain exact
checked no-ops. A recursive semantic frame theorem proves that the entire
ownership traversal preserves globals, world, and trace, allowing the existing
complete `LiveHeapRel.decrementReference_refines` theorem to lift to
`ConcreteRuntimeRel`. The composed rule connects an exact object-like local,
source evaluator, real compiler and adapter, unary host contract, and
continuation; persistent decrements follow the compiler's proved elision path.
Executable guards cover a multi-decrement above one, count-one parent/child
recursive death, and a promoted-tag no-op. The closure descriptor equality is
kept explicit. Unchecked nonpersistent composition and generated artifact
execution remain pending.

W6.6v corrects the cache operation's ownership transition across all runtime
models. The shared FIR runtime, JavaScript semantic host, and concrete
linear-memory host now mark the complete reachable object graph persistent
before publishing its root, using mark-before-descend to terminate on cycles.
Executable regressions cover both a nested constructor/string graph and the
`Std.Format.prettyM` cache reuse that originally produced a dead object.
Because the existing `LiveCellRel` constructors describe ordinary mapped
cells, concrete cache composition now requires the named
`CachePersistenceRefines` boundary instead of reusing an invalid heap frame.
Constructing that boundary from recursive persistent-cell relations remains a
proof-lane follow-up; the executable transition and its failure behavior are
already exact.

W6.6w composes explicit deletion. The concrete Talos host installs the
canonical freed header for an ordinary object without recursively releasing
its fields, matching FIR's distinct `del` semantics. Physical word zero is
accepted only through the shared failed-reset `.erased` relation and remains
an exact no-op; ordinary object decoding is unchanged. A representation-
indexed local theorem eliminates every other lane from semantic success, and
the composed rule connects source evaluation, compiler and adapter output,
the exact unary host call, final runtime relation, and continuation. Executable
guards distinguish nonrecursive parent deletion from recursive decrement and
confirm that erased zero preserves the complete concrete heap. Generated
artifact execution remains pending.

W6.6x composes the concrete sharing query. The Talos host decodes the exact
object-like wasm32 lane and returns Lean 4.32's direct UInt8 result in an i32
lane. The existing whole-heap theorem covers immediate tags, promoted tags,
and ordinary live allocations, distinguishing a unique header from persistent
or multiply referenced objects without changing the runtime witness. The
composed rule connects source evaluation, compiler and adapter output, the
exact unary result-producing host call, destination-local refinement, and an
arbitrary continuation. Executable guards cover a unique ordinary object, the
same object after a reference-count increment, an immediate tag, and a
promoted tag. Generated artifact execution remains pending.

W6.6y composes typed unboxing for the five integer and `USize` kinds supported
by the concrete runtime. An ABI-indexed Talos host returns the exact i32 or i64
lane produced by checked linear-memory decoding. A representation-indexed
premise records the crucial FIR invariant: tagged values are interpreted at
the requested type, while the frozen descriptor of a type-erased heap box
must match the generated result kind. The composed rule connects source
evaluation, compiler and adapter output, the exact unary host call,
destination-local refinement, and an arbitrary continuation. Executable
guards cover all five kinds across immediate, promoted-tag, and ordinary boxed
storage. Float kinds remain tracked by the shared runtime gap, and generated
artifact execution remains pending.

W6.6z composes integer boxing for the same five supported kinds. The concrete
Talos host consumes the exact i32 or i64 scalar lane, selects immediate,
promoted-tag, or ordinary boxed storage from the payload, and returns the
resulting object word. Its refinement grows the witness precisely when the
physical representation allocates, then relates the source runtime/result to
the replaced concrete heap. The composed rule connects source evaluation,
compiler and adapter output, the exact unary host call, object destination
local, and an arbitrary continuation. Executable host round trips cover every
supported kind across all three storage classes. Float kinds remain tracked
by the shared runtime gap, and generated artifact execution remains pending.

W6.6aa composes reset across all three successful runtime branches. The
concrete Talos host returns the physical empty token for immediate values,
performs the checked semantic decrement for nonunique objects, and returns the
original address after a unique constructor enters the cleared reuse protocol.
A witness-transport boundary carries locals, globals, external events, traces,
and both shallow and recursive runtime relations across ordinary heap changes
or the unique descriptor rebind. The composed rule connects source evaluation,
compiler and adapter output, the exact unary host call, reuse-token destination
local, and an arbitrary continuation independently of which reset branch ran.
Executable guards cover immediate, nonunique, and unique behavior. Consuming
the protocol through generated `reuse` and artifact execution remain pending.

W6.6ab composes reuse across fresh empty, fresh nonempty, and in-place paths.
The concrete Talos host decodes the exact reuse-token lane followed by the
compiler-selected wasm32 object fields. Physical token zero selects tagged or
ordinary fresh allocation, while a nonzero token consumes W6.6aa's reset
protocol and rebinds the retained address to the replacement constructor
descriptor. A common runtime frame preserves globals, world, and trace; the
composed rule connects source evaluation, compiler and adapter output, the
arbitrary-arity host call, result-local write, and an arbitrary continuation.
Executable guards cover all three paths, including reset-to-reuse identity of
the retained address. Generated artifact execution remains pending.

W6.6ac begins constructive cache-persistence discharge. The proof boundary is
now an inductive proposition, allowing representation proofs to expose the
post-persistence heap without treating proof evidence as runtime data. A new
`PersistenceCorrectness` layer proves that already-persistent allocations are
exact no-ops at every concrete fuel budget and derives `CachePersistenceRefines`
for every non-heap semantic lane: scalar, erased, reuse token, direct tagged,
and promoted tagged values. Core runtime and Talos cache-set composition rules
consume that theorem directly, so callers no longer provide a persistence
premise for those lanes. Recursive mapped heap graphs remain the next cache
slice; no runtime or shared FIR semantic contract changed.

W6.6ad establishes the first constructive heap-valued cache slice. Common
header decoder frames now support a joint reference-count/persistence rewrite
while compatibility wrappers preserve every existing increment/decrement
theorem. The new persistence layer uses that frame to rewrite any represented
live cell, rebuild the bidirectional whole-heap relation around the changed
allocation, and prove positive-fuel persistence for ordinary boxed scalars and
heap naturals. Their semantic folds contain no heap children, so a fuel-
independence theorem reconciles the concrete cursor bound with FIR's heap-
length bound. Core runtime and Talos cache-set rules consume the resulting
constructive leaf theorem directly. Recursive constructor and closure folds
remain next; no executable or shared semantic contract changed.

W6.6ae establishes the recursive constructor step. ABI-indexed ownership
slots now expose either a mapped heap child or matching concrete/semantic
persistence no-ops for immediate tags, promoted tags, and erased sentinels.
Their ordered relation lifts any correct child recursion through the complete
concrete `foldlM` and semantic heap fold while preserving `LiveHeapRel` after
each child. A constructor theorem combines that fold with W6.6ad's parent
metadata rewrite and proves the exact positive-fuel subgraph transition under
an abstract child-recursion hypothesis. Closure capture filtering and the
global fuel induction remain next; no executable or shared semantic contract
changed.

W6.6af establishes the matching recursive closure step. A pure capture-fold
theorem proves that statically non-owning captures are semantic persistence
no-ops, so the descriptor-filtered concrete child order agrees with FIR's full
capture order. The closure node theorem combines that filter with the common
metadata rewrite and ordered child recursion, retaining explicit descriptor-
table identity. Closing the global induction then exposed
`FIR-BUG-wasm-none-persistence-dead-child-refinement`: `LiveHeapRel` admits a
live parent owning a mapped dead child, which FIR skips but concrete
`readLiveHeader` rejects. The discrepancy is recorded before changing either
the refinement invariant or operation-specific dead handling. No shared FIR
semantic contract changed.

W6.6ag closes that recorded dead-child discrepancy with an operation-specific
canonical released-header branch. Persistence rereads a dead target and
returns unchanged only when every frozen freed-header field and retained extent
is valid; ordinary decoders and malformed dead headers keep their existing
structured failure. Runtime guards cover the accepted and rejected cases, and
`DeadCellRel.markPersistentFuel_eq` plus the whole-heap dead-location theorem
provide the exact recursive induction branch. No shared FIR semantic contract
changed.

W6.6ah closes the complete same-fuel recursive persistence simulation. The
proof counts semantic cells that are simultaneously live and ordinary,
establishes that the parent metadata rewrite removes exactly one, and proves
that every child persistence fold is measure-nonincreasing. Constructor and
closure recursion now thread the resulting remaining-fuel bound, including
cycles, persistent revisits, and canonical dead targets, into a single
`LiveHeapRel.markPersistentFuel_refines` theorem. The concrete zero-fuel fault
for an ordinary live object remains intact; lifting successful semantic heap
fuel to the larger cursor-derived public fuel is the next slice. No executable
or shared FIR semantic contract changed.

W6.6ai lifts that theorem to the public runtime and closes the recursive cache
boundary. Successful `markPersistentFuel` execution is proved monotone in
fuel, so the semantic heap-length result lifts unchanged to the no-smaller
concrete cursor-derived budget while preserving zero-fuel exhaustion on real
ordinary work. `LiveHeapRel.markPersistent_refines` now covers every mapped
constructor, closure, box, and natural graph; `CachePersistenceRefines`, core
global writes, and Talos `cacheSetStep` obtain that proof constructively with
explicit host/witness closure-descriptor identity. No executable or shared FIR
semantic contract changed.

W6.6aj installs the first whole-module concrete resolver. It validates stable
runtime import identities, preserves their positional ABI, constructs a Talos
environment and matching exact-invocation specification from the existing W6
hosts, and proves that the environment satisfies that specification. Natural
literal, constructor/projection, and constructor-case programs now pass the
complete lower/adapt/resolve/execute path with concrete words and host-owned
linear memory. String/scalar literals, floating scalar operations, legacy
`closureApply`, and external imports are rejected at resolution as explicit
fragment gates. The emitted Node/browser artifacts still use the semantic
JavaScript host; switching that external-engine boundary remains separate.

W6.6ak widens that resolver path across the closed supported corpus. Concrete
host initialization now derives typed cache slots from the same source
initializers that create Wasm flag/value globals, allowing a twice-called
cached constructor graph to exercise miss publication, recursive persistence,
and hit reuse. Whole-module executions additionally cover default cases,
direct calls, `USize` and packed scalar access/mutation, object/tag mutation,
integer boxing/unboxing, sharing, checked increment/decrement, deletion, and
both reset/reuse branches. This audit found
`FIR-BUG-wasm-none-scalar-slot-layout-contract`: the shared hand-written
mutation fixture uses index `1` despite a two-slot object/`USize` prefix. The
regression retains its exact structured failure, while a separate index-`2`
fixture follows Lean 4.32 `ToImpure` and passes concretely. No shared contract
was weakened or changed.

W6.6al closes whole-module concrete closure execution. Host initialization now
derives the immutable closure dispatch table from generated-function order and
deduplicates typed capture descriptors in first-use `partialApply` order, the
same deterministic identities stored in concrete closure headers. Ordinary
closure application, erased capture, and successive underapplication fixtures
now lower, adapt, resolve, allocate, match, project, and directly invoke their
callees through Talos with host-owned linear memory; a recursive direct-call
fixture passes through the same initialized store. This crosses the executable
boundary for `partialApply`, `closureMatches`, `closureProj`, and the generated
Wasm trampoline while retaining legacy `closureApply` as a resolver gate. The
complete candidate-fold proof and external-engine artifact switch remain
separate. No shared contract changed.

W6.6am opens the concrete external-engine lane. A browser-safe JavaScript host
implements the proved wasm32 word classification, 32-byte checked header,
eight-byte semantic slots, natural/constructor allocation, and typed closure
capture ABI without runtime handles. Observation-only allocation descriptors
and logical-location identities normalize the physical heap against the live
FIR oracle but are not consulted by generated runtime operations. A dedicated
Node runner now executes 23 closed artifacts covering all direct scalar and
argument lanes, tagged and heap naturals, constructors/cases/projection,
ordinary and recursive direct calls, and single/multi-stage closure
application. Unsupported operations fail during concrete import construction;
the semantic runner remains in parallel for the wider corpus while mutation,
ownership, reset/reuse, strings, externals, initial heaps, and the browser
client are ported in subsequent slices. No shared semantic contract changed.

W6.6an widens that external-engine host across the concrete mutation and
ownership protocol. Checked object-slot and constructor-tag writes now frame
the byte-level header/payload exactly; increment, recursive decrement,
`isShared`, delete, and unique/shared reset/reuse update physical reference
counts and released headers without semantic handles. Four existing artifacts
for object/tag mutation and both reuse branches now pass concretely. Two new
Wasm-specific constructor fixtures exercise balanced increment/decrement,
recursive owned-graph release, and the exact logical-location dead-object
observation after deletion without
weakening the still-gated string representation. A compiler-shaped
packed-layout fixture executes `USize` and `UInt64` write/read at Lean 4.32's
emitted slot index; cached-constructor execution covers miss publication,
recursive graph persistence, and the subsequent hit; and maximum-`UInt64`
fixtures cover both heap boxing and box/unbox round-trip. The Node concrete
allowlist therefore contains 34 artifacts. The malformed historical
scalar-layout fixture remains an exact `scalarFieldMissing(1, 0)` expected
failure tied to its existing bug card; strings, externals, initial heaps, and
browser execution remain subsequent slices. No shared semantic contract
changed.

W6.6ao makes the concrete external-engine lane browser-portable without a
second runtime implementation. Node and a Fetch-only module Worker import the
same `ConcreteHost` and frozen fixture inventory. Chrome executes all 34
live-oracle artifacts plus the two import-construction fragment gates and the
exact malformed-layout expected failure. The browser-enabled artifact gate
materializes only ignored `_build` corpus data, verifies the established
semantic browser clients first, and then checks the concrete byte-memory lane.
Strings, externals, and initial heaps remain subsequent slices. No shared
semantic contract changed.

W6.6ap opens the concrete initial-runtime boundary for the represented
constructor/natural subset. The JavaScript host reserves a physical wasm32
address for every semantic location before installing references, reconstructs
object-field constructors and arbitrary-precision natural limbs, preserves
reference count, persistence, liveness, heap order, and `nextLocation`, and
maps heap-backed entry arguments without opaque handles. The compiler-produced
`List Nat` case audits all four loaded cells and the address round-trip before
executing `getTag` to `UInt64(1)` in Node and Chrome. The string source remains
an exact construction-time layout gate; packed constructors and other initial
heap kinds remain outside this slice. No shared semantic contract changed.

W6.6aq freezes and executes the concrete string layout. A live string is one
ordinary reference-counted object whose payload is the canonical `String.toUTF8`
byte sequence, with `aux0 = 1` as the layout marker, `aux1` as the exact byte
count, and zero reserved metadata; allocation padding is not semantic data.
Lean's concrete runtime and Talos host now allocate this layout, while the
shared Node/browser JavaScript host allocates, validates, observes, and loads
the same bytes. The compiler-produced `string-heap` and mixed `nested-heap`
artifacts move into the concrete success inventory, and the Unicode source
input crosses the former initial-runtime gate after an exact cell/address
audit. Both engines now execute 36 artifacts, retain only the external import
fragment gate, and preserve the historical malformed-layout expected failure.
This slice establishes the executable boundary; integrating string cells into
`LiveHeapRel` and proving fresh-allocation framing remains the next proof
slice. No shared semantic contract changed.

W6.6ar establishes the concrete string allocation proof boundary. The new
proof module shows that the recursive UTF-8 writer installs every byte in
source order, frames every address outside the payload, preserves the common
header and old heap prefix, and retains the allocator frontier invariant. A
successful `allocateString` now yields an exact `StringObjectRel`, including
the version marker, byte count, reserved metadata, aligned extent, reference
count, raw byte decoder, and checked public decoder. The Talos concrete runtime
imports this module so the proof is in its ordinary dependency cone. This is a
foundational allocation slice: descriptor binding, `LiveCellRel`/`LiveHeapRel`
extension, and generated literal composition remain separate follow-ups. No
shared semantic contract changed.

W6.6as adds strings to the proof-only allocation witness. A fresh string now
binds its semantic location and exact source value to the concrete address,
preserves every prior location, promoted-tag, descriptor, dispatch-table, and
capture-descriptor lookup, and retains witness injectivity plus the
location/promoted-address partition. This isolates the ghost-state extension
from the larger `LiveCellRel` exhaustiveness change; the next slice consumes
the new descriptor together with `StringObjectRel` to extend `LiveHeapRel`.
No executable layout or shared semantic contract changed.

W6.6at closes that string-to-heap refinement slice. `StringObjectRel` now
retains the exact allocation extent and UTF-8 payload while leaving mutable
reference-count/persistence metadata to `LiveCellRel`; consequently the same
decoded string survives prefix allocation, ownership writes, and persistence.
Strings join the complete live-cell matrix, descriptor spatial framing,
sharing, checked increment/decrement, canonical count-one release, recursive
release dispatch, cache persistence, mutation exclusion, and reset/reuse
transport. A fresh `allocateString` now extends `LiveHeapRel`, relates the
returned wasm32 `.object` word to the new semantic location, and agrees with
the source string-literal allocation step. Generated literal-`let` composition
remains the next boundary. No executable layout or shared semantic contract
changed.

W6.6au composes compiler-produced string literal `let` bindings with that heap
theorem. The concrete host allocation now extends `ConcreteRuntimeRel`,
returns the exact `.object` wasm32 lane emitted by Lean 4.32 lowering, writes
the fresh address into the compiler-assigned local, transports every existing
local across the witness extension, and resumes an arbitrary recursive
`CodeWP` continuation. A closed Unicode initial-state theorem instantiates the
same allocation boundary. This also tightens W6.6at's result relation from the
wider `.tobject` lane to the compiler's precise `.object` ABI. No executable
layout or shared semantic contract changed.

W6.6av crosses the concrete Talos external-call boundary. The positional
resolver now accepts validated source external imports with exactly one result,
retains their stable import key and source type metadata, and selects an
executable signature-directed host function. That host decodes i32/i64/f32/f64
arguments directly into concrete lanes, invokes an explicitly installed
`ConcreteExternalImpl`, installs its heap/world response, appends the exact
concrete event, and returns a response only when its lane matches the declared
physical result type. The safe default remains reject-by-default.
`externalStep_of_refines` connects the
executable step to the existing request/response witness extension theorem,
and the complete lowered UInt64 echo fixture now resolves and executes with an
exact world increment and trace event. The Node/browser concrete host still
retains its explicit external import gate for the next slice. No shared
semantic contract changed.

W6.6aw closes the matching concrete external-engine gate. The browser-safe
JavaScript host now accepts an explicit reject-by-default external registry,
decodes generated physical arguments through the same concrete heap/value
representation used by runtime operations, invokes the selected handler,
advances the world, records the exact source-shaped event, and encodes the
declared result lane. The semantic and concrete artifact hosts share one
registry definition while retaining independent runtime implementations.
`external-echo` and the twice-called `cached-external` move into the concrete
success inventory, bringing Node and Chrome to 38 artifacts with no remaining
import-construction fragment gate; the latter confirms one foreign call, one
world/trace update, and a physical cache hit. Both engines separately verify
the structured missing-implementation fault. No shared semantic contract
changed.

W6.6ax composes concrete external calls with compiler-produced code. A
host-polymorphic local-get/call/local-set WP consumes an arbitrary typed
argument list and exact singleton response while preserving the caller's
operand tail. `ExternalLetStepSimulates` pairs the interpreter's complete
three-step external protocol with related concrete/source call equations and
the response's witness extension; `codeWP_externalLet` then binds the physical
result and resumes an arbitrary recursive continuation. This closes the
source external call through concrete runtime/world/trace execution to the
compiler-assigned local without introducing semantic handles. No executable
layout or shared semantic contract changed.

W6.6ay closes concrete whole-module and external-engine coverage for the
supported packed-integer width matrix. Three compiler-shaped fixtures add
`UInt8`, `UInt16`, and `UInt32` mutation/readback at the exact scalar slot
following one object and one `USize` field; together with the existing
`UInt64` case they exercise every proved integer `scalarSet`/`scalarProj`
branch through lowering, adaptation, positional host resolution, standard
WebAssembly execution, and the live FIR oracle. The concrete Node/browser
inventory grows from 38 to 41 artifacts. Float scalars remain excluded by
`FIR-BUG-wasm-none-float-runtime-gap`. No shared semantic contract changed.

W6.6az removes the artificial fresh-only restriction from packed-integer
mutation proofs. All four width-specific constructor, complete-heap, concrete
runtime, and generated `sset` composition theorems now require exactly the
source operation's replacement condition: filtering the written slot/offset
leaves no retained field. A reusable lemma discharges that condition for any
history of writes to the same coordinate, and a closed two-write `UInt64`
module confirms that the second value replaces the first through complete
lowering and concrete execution. Framing retained fields at physically
disjoint offsets remains the next scalar proof slice. No executable layout or
shared semantic contract changed.

W6.6ba closes `objectSet` composition for the remaining `LCNF.Arg` branch.
The compiler's erased argument becomes the canonical wasm32 zero, and a new
local/constant exact-host-call WP connects that emitted prefix to the checked
concrete writer. The operation theorem retains exact `.erased` descriptor
typing, so ordinary object decoding is not weakened. A closed module allocates
an erased object slot, overwrites it with erased, projects it, and returns zero
through lowering, adaptation, host resolution, and concrete execution. Since
impure LCNF arguments are either FVars or erased, object-field write
composition now covers the complete argument syntax. No executable layout or
shared semantic contract changed.

W6.6bb closes unchecked nonpersistent decrement composition. The recursive
whole-heap theorem now carries the outer check bit through every ordinary
parent branch while retaining checked recursive child releases, exactly as
both runtimes specify. Public repeated decrement, the concrete Talos host, and
the source/compiler/adapter composition theorem are correspondingly generic.
Successful nonzero unchecked tagged or promoted releases remain excluded by
their exact representation semantics; amount zero remains the shared empty
fold. A closed ordinary-constructor module executes an unchecked release
through the full lowering and concrete-host path. Closure descriptor identity
and all recursive ownership premises remain explicit. No executable layout or
shared semantic contract changed.

W6.6bc opens retained packed-field framing at the wide write boundary. A
successful checked `UInt64` write now preserves every retained semantic
`UInt8`, `UInt16`, `UInt32`, or `UInt64` field whose byte interval is disjoint
from the written eight-byte interval. The constructor proof carries those
readbacks through the concrete byte/word frames; the complete-heap, Talos host,
and generated `sset` composition theorems expose the same condition. A closed
module writes two disjoint `UInt64` coordinates and projects the first value
after the second write. The narrower writers still require same-coordinate
replacement and are the next framing slices. No executable layout or shared
semantic contract changed.

W6.6bd carries retained packed-field framing through the `UInt32` writer. Its
four-byte concrete store now preserves disjoint retained fields of every
supported integer width, and that invariant reaches the complete heap, Talos
host, and generated `sset` theorem. A closed module writes offsets zero and
four, then projects the first `UInt32` after the second write. `UInt8` and
`UInt16` writers still use the same-coordinate replacement boundary. No
executable layout or shared semantic contract changed.

W6.6be carries the same interval invariant through `UInt16`. The byte-level
halfword proof frames disjoint retained `UInt8`, `UInt16`, `UInt32`, and
`UInt64` reads, with complete-heap, Talos-host, and generated-call composition
above it. A two-coordinate module writes offsets zero and two and rereads the
first halfword. Only the `UInt8` writer remains on the same-coordinate-only
boundary. No executable layout or shared semantic contract changed.

W6.6bf completes retained packed-integer framing with `UInt8`. The single-byte
store now preserves every disjoint retained 8/16/32/64-bit observation, and
the invariant composes through the complete heap, concrete Talos host, and
generated `sset` call. A closed module writes adjacent byte coordinates and
rereads the first. All four supported integer writers now accept arbitrary
histories whose retained byte intervals do not overlap the new write; repeated
same-coordinate histories remain a vacuous special case. No executable layout
or shared semantic contract changed.

W6.6bg begins the full structured-fault audit with a newly confirmed scalar
projection discrepancy. FIR records initialized packed coordinates as a
dynamic list and faults when a valid coordinate has never been written; the
concrete layout zero-fills the declared byte region and currently returns
zero. `FIR-BUG-wasm-none-uninitialized-scalar-projection` contains the exact
closed differential reproducer and leaves the semantic fault unchanged. This
blocks complete `scalarProj` fault correspondence until the Wasm fragment
tracks initialization or proves definite writes before projections. No shared
semantic contract changed.

W6.6bh proves the first two operation-specific structured-fault paths.
Semantic object-field and `USize`-field misses on a mapped live constructor now
force the exact same index/declared-size bounds fault from the checked concrete
reader. The result crosses `ConcreteRuntimeRel` and the Talos host as an
unchanged source-classified runtime trap, with executable guards for both
payloads. Other projection failures remain in the conservative partial matrix,
and scalar projection remains blocked by W6.6bg. No executable layout or shared
semantic contract changed.

W6.6bi extends those bounds results to mutation. Object and `USize` setters
reject the same out-of-range coordinates before any concrete store or semantic
heap update. The local constructor relation, complete heap, and Talos host each
preserve the exact index/declared-size source fault; executable guards also
reread the original in-bounds fields after each trap to confirm the failed
operation changed no payload. Other setter failures remain partial. No
executable layout or shared semantic contract changed.

W6.6bj records the next structured-fault blocker without weakening either
runtime. A closed allocate/delete/`isShared` module returns source
`deadObject 0` from FIR, but the concrete live-header path maps
`MemoryError.deadObject address` through generic `liftMemory` into a target
memory trap. `FIR-BUG-wasm-none-dead-object-fault-classification` retains both
executable observations and proposes a witness-indexed address-fault case,
analogous to reference-count underflow, as a coordinated semantic-Wasm-ABI
change. No workaround or shared contract change is included in this slice.

W6.6bk finds the constructor-allocation failure analogue. For a descriptor
expecting one object field and an empty argument array, FIR emits a broad
`malformed` message while the concrete allocator and Talos host emit source
`arityMismatch 1 0`. `FIR-BUG-wasm-none-constructor-arity-fault-classification`
contains adjacent executable guards and confines the gap to invalid arities;
validated compiler-produced calls remain aligned. Resolving the chosen fault
constructor requires a coordinated source/concrete contract commit, so this
slice adds no workaround or shared-contract change.

W6.6bl resolves W6.6bj as an isolated semantic-Wasm-ABI contract change.
`ConcreteAddressFault` now includes dead-object addresses, `liftMemory` maps a
dead live-header read into that source-address channel, and
`ConcreteAddressFaultRel` translates it to FIR's location-indexed
`RuntimeFault.deadObject` through `HeapReferenceRel`. The closed deleted-object
fixture now requires the source-address Talos trap, and
`FIR-BUG-wasm-none-dead-object-fault-classification` is fixed. Other memory
decoder failures remain target-classified. Both feature branches must rebase
on this contract before dependent work continues.

W6.6bm proves the witness-indexed `isShared` failure path enabled by that
contract. A canonical `DeadCellRel` now forces the exact concrete
`sourceAddress (deadObject address)` result; the whole-heap theorem pairs it
with FIR's `deadObject location` under the persistent address mapping; and the
Talos theorem carries both results into the exact source-address host trap plus
`ConcreteErrorSourceRel`. The existing closed deleted-object guard remains the
executable endpoint. No further shared contract or runtime behavior changes in
this proof-only slice.

W6.6bn extends that stale-reference proof pattern to constructor tag
observation and factors out its common heap facts. `DeadCellRel` now exposes
the exact failed live-header read, while `LiveHeapRel.deadCellRel` recovers the
canonical released representation from any mapped semantic cell known dead.
Both sharing and tag proofs reuse those lemmas. `readTag`, FIR `getTag`, and the
Talos `getTag` host now preserve the paired address/location `deadObject` fault
through `ConcreteErrorSourceRel`; a direct allocate/delete/tag guard checks the
executable trap. No shared contract or runtime behavior changes.

W6.6bo carries the same exact stale-reference boundary through object and
`USize` projection. The common constructor-header decoder is now proved to
reject `DeadCellRel` before kind, bounds, padding, or payload inspection; both
checked readers, both FIR projections, and both Talos hosts preserve the
address/location `deadObject` pair through `ConcreteErrorSourceRel`. A combined
allocate/delete/projection guard deliberately supplies out-of-range indices and
still observes dead-object first. No shared contract or runtime behavior
changes.

W6.6bp extends dead-object precedence across all four supported packed-integer
projection widths. The UInt8/16/32/64 checked readers share one whole-heap
theorem with FIR `getScalarField`, and one ABI-kind-indexed Talos theorem
preserves the exact source-address trap for those four kinds. The deleted-object
guard now checks every width at deliberately invalid coordinates. This result
is orthogonal to the live, valid-but-uninitialized coordinate discrepancy in
`FIR-BUG-wasm-none-uninitialized-scalar-projection`; no shared contract or
runtime behavior changes.

W6.6bq extends exact stale-reference correspondence to object and `USize`
mutation. Both checked writers and both FIR setters return their paired
address/location `deadObject` errors before old-field decoding, bounds checks,
or stores; the Talos theorems retain `ConcreteErrorSourceRel`. The deleted-cell
guard supplies invalid indices and confirms both trapped stores leave linear
memory byte-for-byte unchanged. No shared contract or runtime behavior changes.

W6.6br closes the analogous stale-reference path for constructor-tag mutation.
The checked header writer, FIR `setTag`, and Talos host all preserve the exact
address/location `deadObject` pair before tag-width conversion or any header
store. The deleted-cell guard confirms the trapped operation leaves linear
memory unchanged. No shared contract or runtime behavior changes.

W6.6bs closes the stale-reference path for packed-integer mutation at all four
supported widths. The UInt8/16/32/64 checked writers, matching FIR
`setScalarField` calls, and width-specific Talos hosts preserve the exact
address/location `deadObject` pair before scalar-coordinate validation or any
store. The deleted-cell guard checks each exact trap at deliberately invalid
coordinates and confirms byte-for-byte memory preservation. This remains
orthogonal to the live uninitialized-projection discrepancy; no shared
contract or runtime behavior changes.

W6.6bt extends the exact stale-reference boundary through reference-count
ownership. Concrete/FIR increment and every positive-count decrement preserve
the paired address/location `deadObject` fault before count arithmetic,
descriptor processing, recursion, or any header write; the Talos hosts retain
`ConcreteErrorSourceRel`. The deleted-cell guard checks both traps and complete
memory preservation. Zero-count decrement remains the intentionally specified
empty-fold no-op on both sides. No shared contract or runtime behavior changes.

W6.6bu closes the stale-reference path for explicit deletion. A second delete
on an ordinary released allocation preserves the exact address/location
`deadObject` pair through the checked runtime and Talos host before any header
write, and the executable guard confirms complete memory preservation. This
does not weaken the distinct physical-zero erased-sentinel no-op. No shared
contract or runtime behavior changes.

W6.6bv consumes the shared absolute-`USize` slot contract throughout the
concrete runtime and Talos proof stack. Concrete readers and writers validate
the absolute slot against the constructor's object-plus-`USize` range, then
translate to the local payload offset; live success, exact bounds faults, and
dead-object precedence are proved for both projection and mutation. Forced
source recompilation also repaired allocation proofs that had been hidden by
stale proof artifacts, and the compiler-shaped mixed-layout fixture now writes
slot one after its single object field. The shared contract itself came from
`main`; this slice only updates Wasm consumers.

W6.6bw establishes an experimental arbitrary-precision heap-`Int` boundary.
The current implementation stores a sign and a little-endian magnitude behind
a checked integer header; allocation proves frontier validity, old-prefix
framing, exact header facts, and `readInteger` round-trip for positive and
negative multi-limb values. `IntegerObjectRel` is intentionally local and
replaceable: clients may experiment against it, but neither its header lanes
nor its eventual integration into `LiveHeapRel` is a compatibility promise.

W6.6bx makes the pure external-result consequence explicit.
`ConcretePureExternalPost` and `invoke_pure_result_refines` allow the response
heap and refinement witness to grow while proving unchanged concrete/source
worlds and the exact one-event trace appended on each side. The theorem is
result-polymorphic, so heap-backed `Nat`, `Int`, and `String` results use the
same composition boundary; only their allocation-specific
`ConcreteExternalResponseRel` proof changes as layouts evolve.

W6.6by records the current Lean 4.32 packed coordinates used to construct the
`source-pretty-format-coverage` initial heap. The fixture reads back
`Format.group`'s `UInt8` at `(1, 0)` and `Format.align`'s at `(0, 0)` before
artifact emission. These are compiler-derived assertions for the current
experiment, not a stable ABI: the fixture is expected to change when FIR gains
a clearer layout-aware constructor initializer or Lean changes the lowering.

W6.6bz lifts the experimental heap-`Int` decoder into the complete runtime
relation. Exact-value integer descriptors extend well-formed witnesses and
fresh allocation now establishes `LiveHeapRel` plus the related `.tobject`
result. Common-header ownership and persistence rewrites preserve the checked
sign/magnitude decoder; allocation frames, sharing, constructor-only
mutations, and reset/reuse transport cover the new live-cell alternative.
`integerExternalResponse` then instantiates the result-polymorphic pure
external theorem with an unchanged world and exact related trace event. This
is a workable generation boundary, not a frozen layout: the header lanes and
proof surface may change whenever a cleaner implementation warrants it.

W6.6ca closes the compiler-generated closure candidate fold. The lowerer now
names its existing nested candidate-chain function without changing emitted
instructions. `ClosureCandidateCase` pairs every candidate from the exact
compiler enumeration with its adapted numeric matcher/body and concrete
matcher contract. The complete fold adapts through the unreachable fallback;
execution skips an arbitrary nonmatching prefix, selects the first matching
candidate, leaves the suffix unreachable, reloads the dispatch result local,
and resumes an arbitrary surrounding program. A suffix-polymorphic argument
assembly composes ordinary locals and any number of typed capture projections,
then feeds either the concrete `partialApply`/local-write body or the saturated
ordinary-Wasm direct-call/local-write body. The theorem retains the selected
callee/body proof as the interprocedural premise supplied by the existing
fuel-free termination bridge. Existing tagged-result and structured-failure
gaps are unchanged; no shared semantic contract or executable ABI changed.

W6.6cb makes lazy caching's per-declaration proof boundary explicit.
`compileCachedLetValue_adapted` anchors the concrete proof to the lowerer's
exact flag test, miss body, and cached-value reload after Talos adaptation.
`CachedDeclarationBodyWP` requires the generated zero-argument,
singleton-result signature and a concrete `CodeWP` for the declaration body;
an empty-caller-tail proof now lifts to every caller remainder structurally
through Wasm's function postcondition, then supplies the fuel-free direct-call
premise consumed by the existing miss proof. The two physical publication
facts are factored out and feed the existing hit theorem on the next
invocation, with the host state unchanged by that hit. This closes the generic
compiler/body/miss/publication/hit chain; declaration-specific body-package
instances remain incremental composition work. No shared semantic contract or
executable ABI changed.

W6.6cc supplies the first actual cached-declaration body family.
`codeWP_return_to_bodyPost` is the concrete-host base rule for the generated
`local.get; return` suffix: it resolves the source binding to the exact
physical local and establishes the singleton Wasm function postcondition.
`cachedDeclarationBodyWP_naturalLiteral` composes that suffix with the
compiler/adapter natural-literal `let`, concrete heap allocation, monotone
witness extension, and updated source environment. The result is the
zero-argument declaration-body package consumed directly by W6.6cb's
fuel-free call, miss publication, and subsequent-hit chain. Other declaration
body forms remain incremental instances over the same boundary. No shared
semantic contract or executable ABI changed.

W6.6cd extends the first cached-body family across the object lane.
`cachedDeclarationBodyWP_stringLiteral` composes the compiler-generated UTF-8
literal call, checked fresh string allocation, monotone witness extension,
updated `.object` local, and the same exact generated return suffix. Its result
is the identical zero-argument/singleton-result package consumed by W6.6cb,
showing that the cache handoff is representation-polymorphic across the
natural `.tobject` and string `.object` lanes. No shared semantic contract or
executable ABI changed.

W6.6ce packages generated constructor allocation followed by return.
`cachedDeclarationBodyWP_constructor` composes compiler-adapted argument
loads, the concrete `allocCtor` call, source allocation, target local write,
representation-witness transport, and the exact return suffix into the same
cached-body interface. The theorem is representation-polymorphic: its existing
operation/value-refinement premises admit both tagged empty constructors and
fresh heap-backed constructors without teaching the cache layer either
layout. This aligns the proof boundary with the twice-called cached
constructor-graph execution already covered by the concrete artifact lane. No
shared semantic contract or executable ABI changed.

W6.6cf states the concrete program theorem ladder independently of operation
coverage. `SuccessfulDeclaration` joins an actual FIR `ExecEvaluates` witness,
generated-function resolution, compiler/adaptor `CodeWP`, and exact final
runtime/value refinement. Its public theorem yields fuel-free Talos
termination under `RefinedReturnPost`, which includes the complete
`ConcreteRuntimeRel`, clear structured failure, ABI-indexed physical result,
and unchanged caller operand tail. The body judgment supports arbitrary
physical parameters and caller tails; nullary instances convert directly to
and from `CachedDeclarationBodyWP`. `W6-THEOREM-ROADMAP.md` separates this
sound certificate boundary from the syntax-directed construction, whole-export
success, structured faults, W7 runtime linking, and final import-closure
theorems. No shared semantic contract or executable ABI changed.

W6.6cg begins that syntax-directed construction. `ConcreteCodeSimulation`
currently covers generated return, direct non-calling `let`, and no-result
effect nodes. One induction derives the exact concrete `CodeWP` for every
caller tail and successful source evaluation; companion inductions derive the
final runtime relation, clear failure channel, and physical result relation
from the return leaf rather than accepting them as declaration-level
assumptions. `toSuccessfulDeclaration` and `correct` therefore close T2 for
this initial spine. Calls, externals, lazy paths, and cases remain constructors
to add over the same result indices. No shared semantic contract or executable
ABI changed.

W6.6ch extends the same certificate across generated calls, external calls,
and both lazy-cache paths. A single `sourceExternals` index now ties each
source step to the complete source execution. Finite `ExecSteps` prefix
composition replaces the earlier call-free `CodeEvaluates` shortcut, so the
syntax induction directly derives an exact `ExecEvaluates` witness while its
target induction consumes the existing concrete `codeWP_callLet`,
`codeWP_externalLet`, and `codeWP_lazyLet` rules. The final runtime, failure,
and physical-value facts still come only from the return leaf. Case nodes
remain the next T2 constructor family. No shared semantic contract or
executable ABI changed.

W6.6ci completes T2's structural constructor family with concrete case
control flow. `ConcreteCasesStepSimulates` records the source-selected branch
and a caller-tail/postcondition-polymorphic transformer from that branch's
`CodeWP` to the complete generated case chain. `codeWP_cases` exposes the
existing concrete `CaseChainWP` as the enclosing source `.cases` judgment, and
the new `ConcreteCodeSimulation.caseOf` constructor composes both target
correctness and the exact one-step FIR branch selection with its recursive
continuation. The syntax induction now covers every T2 category; the admitted
program fragment remains determined by which operation- and path-specific
step certificates have been proved. T3 whole-export packaging is next. No
shared semantic contract or executable ABI changed.

W6.6cj closes T3 whole-export success. `ConcreteSupportedExport` packages
only static admission, lowering, source-function lookup, Talos adaptation,
concrete-host resolution/alignment, exported-name resolution, generated
function lookup, and the single-result ABI. Its
`toSuccessfulDeclaration` theorem combines that exact exported function body
with T2's `ConcreteCodeSimulation`; its public `correct` theorem yields the
finite FIR `ExecEvaluates` witness together with
`ConcreteExportTerminatesWith` under `RefinedReturnPost`. Thus the target
function and index are selected by the generated module's export table, not
by a fixture-specific body or index. Physical parameters and caller operand
tails remain general. T4 structured-fault correctness is the next proof
milestone. No shared semantic contract or executable ABI changed.

W6.6ck establishes T4's public structured-fault boundary.
`ConcreteTrapsWith` is the fuel-free trap counterpart of Talos's
success-only `TerminatesWith`; `concreteTrapsWith_of_wp_body_at` and
`CodeWP.toConcreteTrapsWith` derive it from a trap-only generated-body weakest
precondition. `RefinedFaultPost` requires the final concrete runtime to refine
the source runtime at the fault point and requires the host failure to be a
runtime `ConcreteError` related to the exact FIR `RuntimeFault` by
`ConcreteErrorSourceRel`. ABI-shape and target memory/global traps therefore
cannot satisfy the theorem. `ConcreteSupportedExport.faultCorrect` lifts the
boundary through the generated export-name lookup. The remaining T4 work is
the syntax-directed fault induction that constructs the source
`ExecEvaluates` witness and trap-only body `CodeWP` from operation-specific
failure certificates. No shared semantic contract or executable ABI changed.

W6.6cl builds T4's syntax-directed fault certificate.
`ConcreteFaultSimulation` starts from a terminal `ConcreteFaultLeaf` and
transports its exact source fault and trap-only target proof backwards through
successful direct lets, internal/closure calls, external calls, both
lazy-cache paths, selected cases, and no-result effects. The six source-prefix
composition lemmas are now observation-polymorphic, so success and fault
proofs share one interpreter-step layer rather than duplicating it.
`ConcreteFaultSimulation.toCodeWP` and `.execEvaluates` derive both dynamic
premises, while `.correct` and
`ConcreteSupportedExport.faultCorrectOfSimulation` deliver the function-index
and generated-export forms of T4. Remaining coverage work consists only of
constructing terminal leaves from the admitted operation-specific failure
theorems and auditing the full supported-fault matrix. No shared semantic
contract or executable ABI changed.

W6.6cm proves T4's first operation-specific terminal leaf. The new generic
`wp_exact_host_call_of_trap` turns an exact contract-governed host trap into a
Talos weakest precondition, while `sourceLetFault_execEvaluates` turns any
direct `evalLetValue` error into the canonical FIR fault observation.
`concreteFaultLeaf_unaryHostLet` factors the shared compiler/adaptor and trap
composition used by unary result-producing imports. Its first instance,
`concreteFaultLeaf_isShared_deadObject`, proves that a stale semantic heap
location passed to generated `isShared` traps with the related concrete
wasm32 address under `ConcreteErrorSourceRel`. This is an actual terminal leaf
consumable by `ConcreteFaultSimulation`, not merely an operation-level host
equation. Projection and mutation failure families remain next in the leaf
matrix. No shared semantic contract or executable ABI changed.

W6.6cn extends T4's terminal leaves across the projection family.
`concreteFaultLeaf_objectProjection_outOfBounds` and
`concreteFaultLeaf_usizeProjection_outOfBounds` preserve the exact FIR slot
index and declared bound through the compiler, numeric adapter, concrete host,
and Talos trap. Their dead-object counterparts prove the stronger precedence
property: liveness is checked before bounds and the concrete wasm32 address is
related to the source heap location. The packed-scalar dead-object leaf proves
the same precedence uniformly for the supported `UInt8`, `UInt16`, `UInt32`,
and `UInt64` result lanes, independently of width and offset. All five are
instances of `concreteFaultLeaf_unaryHostLet` and are directly consumable by
`ConcreteFaultSimulation`. Packed-scalar coordinate faults and the mutation
families remain in the terminal-leaf matrix. No shared semantic contract or
executable ABI changed.

W6.6co extends T4 through generated no-result field mutations.
`wp_effect_localGets_of_trap` proves the stack-polymorphic Talos boundary for
source-order local loads followed by an exact-contract host trap, and
`concreteFaultLeaf_binaryHostEffect` packages it with the finite FIR fault and
the initial refinement witness. Object and `USize` setters now have terminal
leaves for both exact bounds faults and stale-object precedence. Packed-scalar
setters use one `PhysicalValueRel`-indexed leaf that dispatches across the
supported `UInt8`, `UInt16`, `UInt32`, and `UInt64` lanes while retaining the
correct i32/i64 physical operand. All leaves abort before their source or
generated continuation, preserve the unchanged runtime at the fault point,
and are directly consumable by `ConcreteFaultSimulation`. Unary ownership and
tag effects remain in the terminal-leaf matrix. No shared semantic contract or
executable ABI changed.

W6.6cp closes T4's admitted stale-object ownership and tag families.
`concreteFaultLeaf_unaryHostEffect` specializes the exact trap boundary for
generated one-operand effects. Constructor-tag mutation, nonpersistent
increment, positive nonpersistent decrement, and explicit deletion now retain
the witness-related wasm32 address/source location fault and prove that no
continuation or recursive ownership update begins. The matching object-mode
case leaf treats the compiler-adapted alternative chain abstractly after its
`local.get; getTag` prefix, proving that a stale discriminator traps before any
constructor comparison or branch selection. Persistent ownership operations
remain compiler-elided and therefore have no concrete host-fault leaf. All
five new leaves are directly consumable by `ConcreteFaultSimulation`. The
remaining T4 work is a supported-fragment fault audit covering allocation,
reset/reuse, calls, externals, and source-only malformed states. No shared
semantic contract or executable ABI changed.

W6.6cq closes T4's exact foreign-failure boundary and makes the remaining
goal precise. `externalStep_sourceFailure` preserves an installed concrete
external implementation's source-classified error after successful arbitrary-
arity argument decoding, and
`concreteFaultLeaf_external_sourceFailure` composes that trap through the
generated local-load/call/local-set sequence while proving the result write
and continuation unreachable. The final audit now separates T4 source-fault
preservation from T4S target safety: target memory/layout/global/ABI failures
cannot be related to invented FIR faults. Executable regressions record two
admitted blockers. Explicit `.unreach` loses its structured payload in the
native Wasm trap
(`FIR-BUG-wasm-none-unreachable-fault-classification`), and a one-field
allocation reset then reused for a two-field constructor succeeds in FIR but
trips concrete retained-capacity checking
(`FIR-BUG-wasm-none-reuse-capacity-semantic-gap`). `W6-FAULT-AUDIT.md`
records the exact per-family matrix and next proof order. No shared semantic
contract or executable ABI changed.

W6.6cr closes the direct-projection constructor-kind leaves.
`LiveHeapRel.readConstructorHeader_expectedConstructor_refines` proves the
common checked gateway once across immediate and promoted tags plus every
represented live heap-cell shape; its source premise eliminates the genuine
constructor case without assuming a descriptor. Object, absolute-slot
`USize`, and all four supported packed-scalar host operations derive exact
source-classified `expectedConstructor` traps before any index, coordinate, or
payload check. Their compiler/adaptor terminal leaves feed those equations
into `ConcreteFaultSimulation`, retaining the unchanged source runtime and
making the generated result-local write and continuation unreachable. Case
tags, mutation, unbox, and reset/reuse constructor-kind leaves remain separate
because their semantic gateways accept different object subsets. No shared
semantic contract or executable ABI changed.

W6.6cs closes the constructor-kind mutation family. The common checked-header
theorem now drives exact `expectedConstructor` host equations for constructor
tag, object-slot, absolute-`USize`, and all four packed-integer writers. The
object and `USize` leaves compose those equations through generated binary
effect calls; packed mutation uses one `PhysicalValueRel`-indexed leaf across
the UInt8/16/32 i32 lanes and UInt64 i64 lane; tag mutation uses the unary
effect boundary. Every leaf proves the FIR fault at the unchanged source
runtime, the matching source-classified Talos trap, and an unreachable
continuation, with concrete failure occurring before bounds/coordinate checks
or any heap write. Case tags, unbox, reset/reuse, and ownership underflow remain
the next distinct fault families. No shared semantic contract or executable
ABI changed.
W6.6cu closes recursive cache persistence at the public composition boundary.
`CachePersistenceRefines.of_related` selects the already-proved recursive
mapped-heap simulation or the represented non-heap no-op directly from
`ValueRel`; `ConcreteRuntimeRel.writeGlobal_of_related` composes that result
with the typed concrete global update. General Talos
`cacheSetStep_of_refines` no longer asks callers to manufacture a
`CachePersistenceRefines` function or split heap and non-heap values. Its sole
host/witness side condition is exact immutable closure-descriptor-table
identity. A twice-called, two-constructor cached declaration permanently
exercises miss publication, recursive persistence, hit reuse, and both
generated projections through the complete resolver/Talos execution path.
The existing FIR cached-graph and raw concrete header regressions remain the
other two executable views of the same transition. No shared semantic
contract or executable ABI changed.

W6.6ct closes the constructor-kind case-discrimination leaf.
`LiveHeapRel.readTag_expectedConstructor_refines` handles the
representation-polymorphic `.tobject` boundary directly: the FIR failure
premise eliminates immediate and promoted tags, while the heap branch proves
exact rejection for every represented live nonconstructor cell and eliminates
the genuine-constructor branch. The Talos host theorem preserves the
source-classified trap, and the terminal object-mode case leaf proves the
generated `local.get; getTag` prefix traps before any constructor comparison,
alternative selection, or branch body. Stale discrimination remains covered
by its address-related leaf; missing-alternative `invalidCases` remains the
separate structured-unreachable blocker. No shared semantic contract or
executable ABI changed.

W6.6cu closes the reachable typed-unbox structured-fault family.
`LiveHeapRel.readBoxedScalar_deadObject` proves that a stale mapped heap
operand faults at the common live-header gate while preserving its related
physical/source address. `LiveHeapRel.readBoxedScalar_expectedScalar_refines`
eliminates tagged values and genuine live boxes from the source-failure
premise, then proves exact rejection for every represented live non-box heap
shape. The Talos host equations and compiler/adaptor terminal leaves retain
the unchanged source runtime and make the generated result-local write and
continuation unreachable. The admitted `.tobject` relation excludes
`expectedObject`, while `BoxedScalarKind` excludes unknown-type malformed
requests. No shared semantic contract or executable ABI changed.

W6.6cv closes reset's two pre-bounds structured-fault branches. A canonical
released allocation fails at the live-header gate with the exact related
physical/source `deadObject` address. A live, nonpersistent, uniquely owned
nonconstructor passes reset's ownership fallback test and then fails the
constructor-kind gate with exact `expectedConstructor`; stating those
conditions explicitly preserves the operation's precedence, because shared
or persistent objects decrement and return an empty token instead. The Talos
host equations and compiler/adaptor terminal leaves prove both generated
unary calls trap before the reuse-token local write or continuation.
The admitted `.tobject` operand relation excludes `expectedObject`; bounds
and recursive child-release faults remain separate leaves. No shared semantic
contract or executable ABI changed.

W6.6cw closes reuse's two admitted structured-fault branches and adds the
arbitrary-arity result-call trap combinator needed to package them. After
generated token/field local loads and the statically aligned field-arity gate,
a stale mapped nonempty token preserves exact address-related `deadObject`;
a live mapped nonconstructor preserves exact `expectedConstructor` before
retained-capacity checks or heap writes. Both compiler/adaptor leaves prove
the generated result-local write and continuation unreachable. The admitted
reuse-token relation excludes `expectedReuseToken`, and the compiler-selected
arity excludes malformed arity. The retained-allocation-capacity mismatch
remains the separate T4S issue
`FIR-BUG-wasm-none-reuse-capacity-semantic-gap`. No shared semantic contract
or executable ABI changed.

W6.6cx closes reset's exact object-field-bounds branch. The theorem boundary
states the operation's precedence directly: the operand is a mapped live
constructor, nonpersistent, uniquely owned, and its semantic object-field
count is smaller than the requested reset prefix. Constructor layout
refinement identifies that count with the concrete header count, so both
runtimes produce the same `objectFieldOutOfBounds count size` payload. The
Talos and compiler/adaptor leaves prove the trap occurs before any field is
cleared, any child is released, the reuse-token local is written, or the
continuation begins. Recursive child-release faults remain the next reset
family. No shared semantic contract or executable ABI changed.

W6.6cy closes the direct ownership-underflow branch. The existing uniform
ownership-header theorem reduces every represented live heap shape to one
non-promoted header whose persistent bit and reference count exactly match the
semantic cell. For a mapped live, nonpersistent, zero-count cell, every
positive decrement therefore produces the same address-related
`referenceCountUnderflow` before reading ownership metadata or traversing
children. The Talos host equation and compiler/adaptor terminal leaf preserve
that fault through the generated unary call and prove that no header write,
child release, or continuation instruction executes. Faults reached after
releasing a count-one parent remain the next recursive-ownership slice. No
shared semantic contract or executable ABI changed.

W6.6cz adds the reusable recursive ownership-fault fold. Given paired ordered
concrete words and semantic values, any successful prefix of child releases
advances both heaps under `LiveHeapRel`; the first failing mapped child then
determines an exact `ConcreteErrorSourceRel`, and the remaining suffix is not
executed. Non-owning erased, tagged, and scalar slots stay paired no-ops. This
is the inner induction shared by constructor and closure release faults;
parent-release and generated terminal packaging remain the next slice. No
shared semantic contract or executable ABI changed.

W6.6da closes mapped recursive decrement faults. A complete same-fuel
induction relates stale cells, direct underflow, count-one constructor and
closure parent release, and the first failing child after arbitrary successful
ownership prefixes. Non-fuel concrete errors are proved monotone when the
cursor-derived runtime supplies more recursion budget; repeated decrements
likewise preserve the first fault after successful earlier repetitions. The
public Talos theorem and compiler/adaptor leaf retain the exact
`ConcreteErrorSourceRel`, explicit closure-descriptor identity, unchanged
observable failure state, and unreachable continuation. Release-fuel
exhaustion remains target-classified T4S work; unchecked tagged operand faults
and reset's child-release wrapper remain separate T4 leaves. No shared semantic
contract or executable ABI changed.

W6.6db closes unchecked tagged ownership faults. Both immediate and promoted
physical tags already share one refinement theorem: checked ownership is a
no-op, while unchecked ownership produces `expectedHeapReference`. The new
Talos equations and compiler/adaptor terminal leaves cover arbitrary
increment amounts and every positive decrement amount, whose first repetition
faults before any header access, recursive release, or continuation. A
zero-amount decrement remains the specified empty fold. The `.tobject`
relation excludes `expectedObject`, while delete's stricter `.object`
relation excludes tagged operands entirely. No shared semantic contract or
executable ABI changed.

W6.6dc closes recursively mapped child faults for unique-constructor reset.
A public checked ownership-fold theorem threads every successful earlier
child through related protocol heaps, preserves the first non-fuel mapped
fault, and prevents later children from running. Reset temporarily rebinds
the cleared parent descriptor while traversing that prefix, then projects the
fault back to the unchanged location witness; because both reset runtimes are
pure `Except` computations, a failure traps from the original related store
and never writes the reuse-token local or enters the continuation. The heap,
Talos-host, and compiler/adaptor terminal theorems are all general in the
exact mapped child fault. Their explicit `expectedObject` exclusion exposed
`FIR-BUG-wasm-none-reset-erased-child-release`: erased constructor slots are
ABI-admissible, but FIR reset's `decValueOnce` faults while concrete checked
decrement skips physical zero. The proof does not weaken either runtime;
nonunique fallback decrement and release-fuel target-safety remain next. No
shared semantic contract or executable ABI changed.

W6.6dd closes reset's nonunique fallback-decrement fault wrapper. Once a live
mapped cell has a semantic reference count different from one, the physical
ownership header takes the same fallback gate. Any non-fuel source fault from
the delegated public checked decrement is then preserved by the existing
general decrement theorem, and the reset wrapper produces the same
source-classified Talos trap. The compiler/adaptor terminal leaf proves that
neither the empty reuse-token local nor the continuation is reached. This
branch needs no new recursive ownership induction and does not inspect
constructor shape or fields. Release-fuel target-safety is now the remaining
ownership wrapper obligation; the erased unique-child semantic mismatch
remains isolated in its confirmed bug card. No shared semantic contract or
executable ABI changed.

W6.6de closes recursive-release fuel target safety. A live-cell termination
measure proves that FIR's public heap-length budget cannot expose its private
release-fuel marker: every genuine recursive descent marks the parent dead
first, and successful sibling prefixes never increase the measure. Success
and exact non-fuel fault refinement then exclude the concrete
`releaseFuelExhausted` target error for one public decrement and every finite
repetition. An ownership-list theorem carries that result through reset's
cleared-prefix protocol without excluding erased slots, and a complete mapped
reset theorem covers dead, fallback, nonconstructor, bounds, and in-bounds
unique-constructor branches. Matching Talos theorems exclude the structured
target trap from generated decrement and reset host calls. The experimental
zero-fuel primitive regression remains intentional; only public related
operations receive the adequacy guarantee. No shared semantic contract or
executable ABI changed.

W6.6df establishes a workable retained-capacity boundary for admitted
reset/reuse code. A conservative wasm32 analysis records direct constructor
allocations as either definitely producing an empty reset token or retaining
at least their concrete aligned allocation size. Reset transports that
evidence to the token; reuse is admitted only for an empty token or when the
replacement layout fits the retained lower bound, and a fitting result carries
the replacement bound into subsequent reuse. The extraction theorem exposes
the exact inequality already required by
`LiveHeapRel.reuseObject_some_refines`. Both `WasmSupported` and
`validateSupported` reject the recorded one-field-to-two-field
counterexample, while raw lowering retains its exact target-trap regression;
the fitting and shared-reset programs remain admitted. Unknown provenance and
join-parameter token transport are conservatively rejected for now. This is
an intentionally unstable proof boundary that may be widened with stronger
provenance results; no FIR semantic contract or executable ABI changed.

W6.6dg gives that static boundary a concrete dynamic meaning. The
`ReuseCapacityValueRel` invariant covers constructor values and reset tokens:
definitely-empty evidence is represented by a tagged object or the zero token,
while retained evidence on a heap value names a readable allocation header whose
allocation realizes the tracked lower bound. Combining this relation with the
validator's fitting fact now derives the exact `layoutFits` inequality at the
physical token address. `reuseStep_some_of_capacityEvidence` consumes those
two facts and invokes the existing in-place reuse refinement with no free
capacity premise. The remaining syntax work is to preserve
`ReuseCapacityValueRel` across constructor, reset, and reuse steps and attach
it to `ConcreteCodeSimulation`; no FIR semantic contract or executable ABI
changed.

W6.6dh lifts the per-value capacity meaning to the static analysis state.
`ReuseCapacityFactsRel` resolves every tracked source binding at its
compiler-assigned local, while `ReuseCapacityStateRelated` strengthens the
existing W6 state invariant with that whole-map interpretation.
`HeaderCapacityTransport` isolates the precise heap-step obligation: payload,
liveness, and ownership metadata may change, but an existing allocation header
must remain readable with the same retained extent. Generic transport and bind
theorems preserve all old facts across such a heap/witness transition and add
the newly tracked constructor/reset/reuse result; a fitting token can then be
resolved directly from the strengthened state. The next syntax slice must
instantiate header-capacity transport for each operation family and thread
the analysis state through `ConcreteCodeSimulation`. No FIR semantic contract
or executable ABI changed.

W6.6di scopes header-capacity transport to allocation headers that are both
represented by the refinement witness and owned below the current heap
frontier. This avoids an unnecessarily global claim about arbitrary readable
memory while retaining exactly the premise needed by tracked reuse facts.
Fresh prefix extension now instantiates the boundary for nonempty constructor
allocation and for nonempty reuse from the physical zero token. A unique-reset
bridge converts retained object evidence into same-address reuse-token evidence
when the reset operation supplies witness and header transport. The remaining
operation work is in-place reuse, the empty/tagged allocation branches, and
ownership or mutation transitions that can affect represented allocations.
No FIR semantic contract or executable ABI changed.

W6.6dj discharges the in-place reuse transport itself. The concrete
`MappedHeaderCapacityTransport` boundary is now stated at the heap layer:
every semantic location already mapped by the witness keeps the same physical
allocation extent. The byte transaction proves this by preserving the target
header's allocation word and using descriptor disjointness to frame every
other mapped allocation. `reuseObject_some_refines`, its Talos operation
wrapper, and the validator-backed capacity theorem expose that transport
alongside their existing result, witness, runtime, value, and semantic
equations. The remaining operation work is unique reset's concrete
header-preservation instance, the empty/tagged branches, and ownership or
mutation transitions needed by the syntax-directed state invariant. No FIR
semantic contract or executable ABI changed.

W6.6dk discharges unique reset's concrete transport. The boundary now lives
in the common heap-refinement layer and composes across same-extent header
writes, bounded constructor-field writes, and recursive ownership folds.
Unique reset exposes the resulting transport through both the concrete heap
theorem and the Talos host theorem; the validator-backed wrapper carries a
retained constructor bound directly to the returned nonempty reuse token.
Compatibility wrappers preserve the existing decrement theorem surface for
clients that need only `LiveHeapRel`. The remaining transport work is the
empty/tagged allocation branches and ownership or mutation transitions needed
by the syntax-directed state invariant. No FIR semantic contract or
executable ABI changed.

W6.6dl discharges empty/tagged constructor transport. `encodeTagged` now has
one common capacity theorem covering both physical cases: an immediate result
is a heap identity transition, while a promoted tag is a fresh prefix
extension. The result is lifted through empty `allocCtor` and empty-token
`reuse`; their Talos capacity wrappers realize the validator's `emptyToken`
fact while preserving every older retained extent. Forced recompilation also
repaired two stale reset-fault destructurings after W6.6dk strengthened the
reset-prefix result. Ownership and mutation transitions are now the remaining
transport instances before `ReuseCapacityStateRelated` can be threaded
syntax-directly. No FIR semantic contract or executable ABI changed.

W6.6dm discharges ownership-transition transport. Increment and explicit
delete are same-extent header writes (or exact no-ops), while repeated
decrement composes the already proved capacity result for each recursive
ownership step. The concrete heap theorems and Talos operation wrappers now
return `MappedHeaderCapacityTransport` for every successful ordinary,
tagged, promoted-tag, and erased lane; compatibility wrappers retain the
preexisting refinement API. Only payload/header mutation transitions remain
before `ReuseCapacityStateRelated` can be threaded syntax-directly. No FIR
semantic contract or executable ABI changed.

W6.6dn discharges mutation-transition transport. One generic theorem turns a
`TargetMutationFrame` into mapped-header capacity preservation: the target
header is unchanged, while descriptor disjointness frames every other mapped
allocation. Object, `USize`, and all four packed-integer setters consume that
theorem; constructor-tag mutation consumes the existing same-extent
header-write theorem. Concrete heap and Talos operation refinements expose
the transport, and compatibility wrappers preserve the preexisting APIs.
The operation-level transport inventory is complete; the remaining capacity
work is to thread `ReuseCapacityStateRelated` through syntax-directed
execution. No FIR semantic contract or executable ABI changed.

W6.6do threads that inventory through the complete no-result effect spine.
Ownership and mutation `EffectStepSimulates` theorems now expose mapped-header
capacity transport alongside their source, compiler, and weakest-precondition
simulation; compatibility wrappers preserve the existing theorem surface.
Generic transport, effect-step, and heap-replacement adapters reconstruct
`ReuseCapacityStateRelated` at continuation nodes, while persistent ownership
effects use reflexive transport because their concrete heaps are unchanged.
The remaining syntax work is the result-producing let spine: constructor,
reset, and reuse insert new facts, while ordinary results erase or bind facts
before branch and call propagation. No FIR semantic contract or executable
ABI changed.

W6.6dp establishes the result-binding core and closes the tracked operation
inventory. Generic `ReuseCapacityFactsRel` and `ReuseCapacityStateRelated`
rules now insert a proved result fact or erase a shadowed stale fact while
transporting all other facts through the source binding, checked destination
local write, witness transition, and heap transition. Specializations consume
the existing `LetStepSimulates` surface for wasm32 tracked results and
arbitrary ordinary results. Direct constructor allocation, reset, and reuse
now supply the exact evidence selected by `reuseCapacitySafeCode` in every
successful physical branch. In particular, nonunique reset exports
mapped-header capacity transport instead of losing it at the host wrapper,
and unique reset returns both its retained result fact and transport for
unrelated facts. The remaining syntax work is to instantiate these adapters
for each direct-let lowering, then propagate the strengthened state through
branches and calls. No FIR semantic contract or executable ABI changed.

W6.6dq normalizes the direct-result syntax boundary. A generic tracked-source
resolver now identifies the exact concrete lane for any fact, with fitting
reuse as a specialization. Constructor, reset, and reuse each have a named
`LetStepSimulates` adapter whose post-state facts exactly match the static
validator transfer; constructor and tracked/untracked reset heads expose the
corresponding continuation-safety premise. Ordinary result lets share two
erasure adapters: one for a heap-preserving step and one for a fresh prefix
extension. Boxing and natural literals prove capacity transport uniformly
across immediate, promoted, and heap representations; string literals and
partial applications instantiate fresh-prefix transport. This covers every
current direct-let result family without adding transport to the shared
`LetStepSimulates` contract. The remaining proof is the recursive
capacity-aware code certificate, followed by its branch and interprocedural
cases. No FIR semantic contract or executable ABI changed.

W6.6dr defines the recursive theorem target for capacity-safe execution.
`reuseCapacityLetFacts?` is now the authoritative, behavior-preserving static
transfer used by `reuseCapacitySafeCode`, so proof code no longer duplicates
the validator's constructor/reset/reuse match. The new
`ReuseCapacityCodeSimulation` mirrors `ConcreteCodeSimulation` across direct
lets, calls, externals, lazy-cache paths, cases, and no-result effects while
indexing every node and the selected return leaf by their exact fact maps. It
records static acceptance and the dynamic `ReuseCapacityStateRelated`
interpretation at each recursive boundary. Erasure recovers the existing
executable simulation, and therefore its `CodeWP` theorem, without changing
endpoints. The remaining W6 work is constructive: build this certificate from
the operation-specific result/effect transitions and close the
interprocedural call transition, then lift it to the supported export theorem.
No FIR semantic contract or executable ABI changed.

W6.6ds connects that certificate to the generated-export boundary. The empty
validator fact map adds no obligation beyond the ordinary initial concrete
state relation. A completed `ReuseCapacityCodeSimulation` can therefore erase
to the existing successful-declaration theorem, while the strengthened export
theorem additionally exposes the selected return state's exact final fact-map
interpretation. This lift deliberately consumes, rather than postulates the
automatic construction of, the syntax certificate. The remaining proof work
is to assemble its operation-specific nodes and state the capacity-preserving
interprocedural call condition explicitly. No FIR semantic contract or
executable ABI changed.

W6.6dt makes that interprocedural condition explicit and reusable.
`ReuseCapacityResultStep` pairs any existing result-step simulation with the
exact strengthened relation before and after the validator-selected fact
transfer. Named direct, external, lazy, and call specializations are consumed
by the recursive certificate; generic constructors cover both tracked-result
insertion and ordinary-result erasure. The call erasure theorem isolates the
three facts not exported by `CallLetStepSimulates`: the checked destination
write, witness transport, and retained-header transport. Canonical return,
selected-case, and transported-effect builders remove the remaining
certificate boilerplate. The next call slice must obtain those three facts
from the concrete callee theorem rather than weakening the capacity relation.
No FIR semantic contract or executable ABI changed.

W6.6du proves the first hereditary interprocedural instance. Every recursive
capacity certificate now composes its per-step witness and retained-header
transports into one end-to-end frame theorem. A
`CapacityPreservingSuccessfulDeclaration` packages that frame with the
existing exact declaration execution theorem, and supported exports obtain
the package directly from their capacity-aware body certificate. The direct
named-call constructor uses argument assembly, exact callee termination, the
checked result-local write, and the callee frame to build both the ordinary
call simulation and its validator-selected erasure result step; a companion
builder inserts it into the recursive certificate. The remaining
interprocedural work is to instantiate the same hereditary boundary for
closure dispatch, lazy caches, and external calls, then finish automatic
syntax-directed certificate construction. No FIR semantic contract or
executable ABI changed.

W6.6dv closes the saturated closure-dispatch instance. The proof follows the
compiler's exact candidate chain: any nonmatching prefix executes only
read-only matcher calls, the selected candidate assembles projected captures
and explicit arguments, and its ordinary declaration call consumes the same
hereditary callee certificate as a named call. Two small structural lemmas
show that normal fallthrough crosses every nested candidate resumption layer
and that the candidate's result-local store followed by the dispatch reload
and enclosing `let` store is a checked idempotent write. The resulting
capacity-aware call step retains all caller facts except the bound result,
and a recursive builder derives the numeric Talos dispatch adaptation from
the compiler candidate list. Underapplication remains a fresh-allocation
result path rather than an interprocedural callee path; lazy-cache and external
call instances, followed by automatic syntax-directed certificate assembly,
remain. No FIR semantic contract or executable ABI changed.

W6.6dw closes partial application and closure underapplication. One concrete
allocation theorem now packages the partial-application host return, extended
closure witness, related semantic result, clear failure channel, and
fresh-prefix retained-header transport. Direct `.pap` lets consume that
package as an ordinary allocating result step. For a source closure
application, the selected underapplication candidate feeds its projected
captures and explicit arguments to the same package; the existing matcher
chain, nested branch resumption, dispatch-local reload, and enclosing
destination write then produce a capacity-aware call step. The recursive
selected-dispatch builder is intentionally agnostic between saturated
declaration calls and underapplication allocation. Lazy-cache and external
call instances, followed by automatic syntax-directed certificate assembly,
remain. No FIR semantic contract or executable ABI changed.

W6.6dx corrects the program-proof endpoint before further certificate
assembly. FIR controls this compiler, so caller-supplied
`ConcreteCodeSimulation` or `ReuseCapacityCodeSimulation` values must not be
the final correctness boundary. `ConcreteSupportedExport` now retains the
actual `compileCode`/adapter equation for its selected body and a static
lowering-context/function-local alignment invariant. The new
`ConcreteCompilerCorrectness` module inverts those executable equations for a
source return and proves exported concrete execution directly from a source
evaluation and the initial state relation. A separate compile-time contract
module applies the theorem without any translation-certificate premise.

The pragmatic next endpoint is conditional preservation of finite source
returns and faults; it does not assert that source programs terminate. The
next proof slice is the direct-`let` compiler rule, instantiated first by
literal operations. Existing `CodeWP`, successful-declaration, fault, and
capacity certificate modules remain internal compatibility scaffolding while
their operation and transport lemmas move beneath the direct structural
theorem. Once the finite compiler theorem covers the supported fragment, add
a Talos relational-execution adequacy layer and lift the same state relation
to finite traces, divergence preservation, and weak simulation/bisimulation
as useful. No FIR semantic contract or executable ABI changed.

W6.6dy supplies the first compositional theorem on that corrected path.
`ConcreteSupportedExport` now also records static runtime-call alignment:
symbolic call indices, adapted import slots, resolved concrete contracts, and
their arities agree. `CodeAdapted.naturalLiteralReturn_eq` inverts the actual
compiler and adapter to recover the exact
`call; local.set; local.get; return` body. The public
`correctNaturalLiteralReturn` theorem then composes concrete natural
allocation, witness extension, the checked local write, and the return suffix
to prove matching finite source execution and exported target termination.
The caller supplies no syntax simulation or translation certificate; only
allocation success and local-write capacity remain dynamic preconditions.
The compile-time contract harness covers this API. The next proof slice
generalizes the immediate-return continuation, adds UTF-8 strings, and then
moves to constructor/projection lets. No FIR semantic contract or executable
ABI changed.

W6.6dz generalizes the immediate-return continuation. `CodeAdapted.let_eq`
inverts every successful direct `let` through both executable compilation
stages, recovering separately compiled/adapted value and continuation
fragments plus the adapter-selected destination slot.
`CodeAdapted.naturalLiteralLet_eq` resolves the literal prefix and local kind,
and `ConcreteSupportedExport.codeWP_naturalLiteralLet` composes allocation,
witness extension, the checked destination write, and an arbitrary
compiler-selected continuation correctness hypothesis. That hypothesis is
the recursive semantic induction hypothesis, not a translation certificate.
The earlier immediate-return inversion is now a corollary of the general
split, and the compile-time contract harness applies the recursive API
without `ConcreteCodeSimulation` or `ReuseCapacityCodeSimulation`. UTF-8
strings are the next direct-let instance, followed by the structural
source-evaluation induction and constructor/projection lets. No FIR semantic
contract or executable ABI changed.

W6.6ea instantiates the corrected direct-compiler path for UTF-8 String
literals. Static resolver alignment now yields the exact concrete
`stringLiteralContract`. `CodeAdapted.stringLiteralLet_eq` derives the
compiler-selected `.object` host call, numeric import/local slots, and
independently adapted continuation from the general direct-`let` inversion.
`ConcreteSupportedExport.codeWP_stringLiteralLet` composes exact UTF-8 heap
allocation and witness extension with an arbitrary continuation correctness
hypothesis, while `correctStringLiteralReturn` packages the immediate-return
case into finite source evaluation and exported target termination. The
contract harness applies both String APIs without a caller-built simulation
certificate. Constructor/projection direct lets and the structural
source-evaluation induction are next. No FIR semantic contract or executable
ABI changed.

W6.6eb extends the certificate-free direct-compiler path to constructor
allocation with ordinary `fvar` fields. A new adapter inversion determines the
numeric local-get prefix and constructor import directly from successful
adaptation; `ConcreteSupportedExport.allocCtorCall` recovers the exact concrete
resolver contract and arity. `constructorFVarLet_eq` and
`codeWP_constructorFVarLet` then compose the compiler-selected argument slots,
allocation, witness extension, destination write, and an arbitrary continuation
correctness hypothesis. `correctConstructorFVarReturn` closes the corresponding
finite exported execution, and the contract harness applies both public APIs
without a caller-built translation simulation. This is deliberately the
current all-`fvar` argument boundary: erased fields compile to constants and
need the next generalized argument-prefix proof. Projections and the structural
source-evaluation induction follow. No FIR semantic contract or executable ABI
changed.

W6.6ec removes that all-`fvar` boundary. `ConstructorArgsCompiled` now
characterizes the executable `compileArgs` fold itself, including both local
reads and erased-field constants. Successful source evaluation, real
adaptation, `LocalLayoutAligned`, and `StateRelated` derive a
`ConstructorArgsReady` target prefix and its physical arity; callers no longer
supply argument indices, local-read evidence, or a translation witness.
`constructorLet_eq`, `codeWP_constructorLet`, and
`correctConstructorReturn` lift the mixed prefix through arbitrary
continuations and finite exported execution. The concrete allocation boundary
remains intentionally operation-polymorphic: it is invoked at the physical
operands produced by the compiler/evaluator proof. No FIR semantic contract or
executable ABI changed.

W6.6ed moves all three projection forms onto the same certificate-free
recursive path. One generic `localRuntimeCallLet_eq` theorem inverts the
production shape shared by object, `USize`, and packed-scalar projections:
one compiler-selected source local, one resolved runtime call, one destination
write, and an independently compiled continuation. The three public
`codeWP_*ProjectionLet` rules recover their numeric locals, import, exact host
contract, and physical object operand from `ConcreteSupportedExport`,
`LocalLayoutAligned`, and `StateRelated`. Object and `USize` reads require only
the constructor-descriptor invariant needed by the existing heap theorem;
packed-scalar reads expose one operation-specific refinement at the derived
object word. The contract harness applies every rule with arbitrary
continuations and no caller-supplied target program, local/import indices,
host contract, or translation simulation. The next step is to assemble these
direct-value rules into the structural source-code induction. No FIR semantic
contract or executable ABI changed.

W6.6ee supplies that first structural induction. `DirectValueEvaluates` is a
source-only finite evaluation relation for return and direct-value `let`
spines, with a proof that it embeds in the existing `CodeEvaluates` semantics
and hence in executable `ExecEvaluates`. `DirectLetRuntimeRefines` states the
uniform condition that the runtime must prove: for every admitted successful
source step and every value prefix accepted by the production compiler and
adapter, concrete execution establishes `LetStepSimulates` and preserves a
caller-chosen resource invariant. It universally quantifies the emitted value
program and numeric destination local rather than storing either as a
translation witness. `codeWP_of_directValueEvaluates` then inducts over an
arbitrarily long direct-value spine, inverts `compileCode`/adaptation at every
node, threads the related concrete state, and derives the exact final
function-body postcondition, runtime relation, clear failure channel, and
ABI-indexed result relation. The compile-time contract harness applies this
theorem without `ConcreteCodeSimulation` or another source/target certificate.
The next slice discharges the uniform runtime law from the existing
literal/constructor/projection refinements for the currently admitted
direct-value fragment, then extends the induction with effects and control
flow. No FIR semantic contract or executable ABI changed.

W6.6ef supplies the first constructive instance of that uniform runtime law.
`LocalAliasSupported` admits zero-argument `.fvar` declarations only when the
source and destination have the same compiler-selected ABI kind; it contains
no target instructions or numeric local indices. `ConcreteLocalFrameAligned`
separates the missing resource fact from semantic refinement by recording the
exact parameter/local frame lengths. A generic lookup-bound theorem makes
every compiler-resolved destination valid, Talos `set?` preserves the frame
shape, and `directLetRuntimeRefines_localAlias` derives the emitted
`local.get`, adapted numeric source slot, copied physical lane, destination
slot, and `local.set` simulation from the production compiler/adapter plus
`StateRelated`. The contract harness composes two aliases and a return through
the structural theorem, demonstrating that the runtime-law interface scales
past one-node declarations without certificates. The next slice generalizes
this resource instance across read-only projections. No FIR semantic contract
or executable ABI changed.

W6.6eg removes redundant constructor-descriptor readiness from that projection
boundary. A successful semantic constructor decode at a related object word,
together with `ConcreteRuntimeRel`, now recovers the constructor descriptor
already carried by the whole-heap relation. The object- and `USize`-projection
corollaries reuse that fact directly. Consequently,
`codeWP_usizeProjectionLet` exposes no heap-shape premise, while
`codeWP_objectProjectionLet` exposes only the selected field's ABI-kind
agreement—the genuine compiler-typing obligation needed to relate the
physical word. The public contract harness checks both reduced APIs. The next
slice constructs the uniform `DirectLetRuntimeRefines` instance for read-only
`USize` projection from this boundary and exact local-frame capacity. No FIR
semantic contract or executable ABI changed.

W6.6eh constructs the first heap-reading instance of the uniform structural
runtime law. `USizeProjectionSupported` records only the source projection,
compiler-selected object/result ABI kinds, and the object-to-`tobject`
refinement; it contains no numeric local, import, target instruction, concrete
word, or descriptor. Successful `SourceLetResult` is inverted to the exact
object lookup and `USize` read. Production compilation/adaptation then
determines the numeric object slot and runtime import, `StateRelated` resolves
the physical object word, `ConcreteRuntimeRel` supplies its constructor
descriptor, and exact frame capacity makes the generated i64 destination
write total. `ConcreteSupportedExport.directLetRuntimeRefines_usizeProjection`
therefore discharges `DirectLetRuntimeRefines` for arbitrarily long admitted
projection spines, and the contract harness applies the structural theorem
without a translation certificate or heap-shape premise. Object projection is
next; unlike `USize`, it retains selected-field ABI-kind agreement as a static
typing obligation. No FIR semantic contract or executable ABI changed.

W6.6ei constructs the object-projection instance and the first mixed
structural admission. `ObjectProjectionSupported` records the source/compiler
shape and a target-independent typing theorem: whenever the projected source
object is related to a constructor descriptor, the selected descriptor field
has the compiler's result ABI kind. Runtime descriptor existence, the concrete
field read, physical result word, numeric locals/import, and checked write are
all derived. `DirectLetRuntimeRefines.or` combines operation families that
preserve the same resource invariant, and `ReadOnlyDirectSupported` now admits
arbitrarily interleaved local aliases, `USize` projections, and object
projections. The contract harness applies one structural theorem to that
mixed spine with no target-code, numeric-layout, concrete-read, or descriptor
witness. Packed-scalar projection is next; its existing operation theorem
still exposes a concrete-read premise that must be reduced to a stable source
typing/layout boundary before joining the uniform law. No FIR semantic
contract or executable ABI changed.

W6.6ej constructs the successful packed-integer projection instance.
`ScalarValueKind` is the sole additional source typing boundary: it relates
the semantic `UInt8`, `UInt16`, `UInt32`, and `UInt64` scalar constructors to
the corresponding compiler ABI lanes without mentioning target code or heap
addresses. A single `scalarProjStep_of_refines` theorem combines the four
existing concrete read refinements. Successful source evaluation supplies the
initialized coordinate and exact scalar; compilation, adaptation,
`StateRelated`, and exact frame capacity supply every target operand, import,
read step, physical result, and destination write. `ReadOnlyDirectSupported`
now admits arbitrary interleavings of aliases and all three projection
families. This is deliberately successful-step partial correctness:
`FIR-BUG-wasm-none-uninitialized-scalar-projection` still records why a
source-failing uninitialized coordinate cannot yet have exact concrete fault
correspondence. No FIR semantic contract or executable ABI changed.

W6.6ek adds the complete nonallocating literal family to the same structural
theorem. `ImmediateLiteralKind` classifies `UInt8`, `UInt16`, `UInt32`,
`UInt64`, and `USize` literals by their exact compiler ABI kind. Its derived
functions determine the symbolic constant, adapted Talos instruction,
physical lane, and semantic value; clients supply none of those as
translation evidence. `directLetRuntimeRefines_immediateLiteral` proves the
constant/write step using only exact local-frame capacity, and
`ReadOnlyDirectSupported` now permits these literals to interleave with
aliases and all three projection families. The audit also identifies the next
resource boundary precisely: constructors, heap `Nat` values, and strings
cannot use this invariant because source allocation is unbounded while the
wasm32 heap is finite. Their structural law must thread a remaining-capacity
condition rather than assume concrete allocation totality. No FIR semantic
contract or executable ABI changed.

W6.6el establishes that finite-heap boundary and applies it to the first
allocating compiler theorem. `MemoryState.AddressSpaceBudget` records
source-computed, already-aligned wasm32 headroom; linear memory needs no
separate capacity premise because the concrete allocator grows it on demand.
`AllocationCapacity` is the one-request view. The raw and object allocators
are now proved constructive from an aligned live frontier and that capacity,
and the budget-consumption theorem subtracts the exact aligned request for
later structural composition. The UTF-8 layer derives its checked 32-bit byte
count, object allocation, and complete payload write from the same boundary.
Consequently, both `codeWP_stringLiteralLet` and
`correctStringLiteralReturn` no longer assume an opaque
`allocateString = .ok ...` execution witness: they assume only explicit
address-space capacity, obtain alignment from `StateRelated`, and construct
the concrete allocation themselves. This surface is intentionally
experimental; the next slice computes and threads path budgets through
allocating direct-value evaluation, then applies the same boundary to
constructors and heap-backed naturals. No FIR semantic contract or executable
ABI changed.

W6.6em applies the same finite-resource boundary to nonempty constructors.
`allocateConstructor_nonempty_eq_ok_of_capacity` computes the exact aligned
request from `ConstructorLayout`, constructs the checked object allocation,
and proves every decoded object-field write lies inside that extent.
`allocCtorNonemptyStep_of_refines_of_capacity` lifts this result through the
concrete host/source refinement boundary: the resulting heap, address,
witness extension, target return, and source `allocCtor` step are all
constructed from the static layout capacity. The older equation-driven
operation theorem remains an internal factoring lemma; compiler clients no
longer need it once their argument relation supplies decoded fields. W6.6en
performs that compiler lift. This resource surface remains experimental, and
no FIR semantic contract or executable ABI changed.

W6.6en removes the opaque constructor-step premise from the public recursive
and finite nonempty-constructor compiler theorems.
`ConstructorArgumentsRelated` is derived alongside
`ConstructorArgsReady` from the production compiler, adapter, evaluator, and
`StateRelated`; erased arguments contribute the canonical related zero word,
while locals retain their exact `PhysicalValueRel`.
`decodeObjectWords` proves that the generated operation's object-field ABI
condition forces every operand onto its i32 word lane, constructively
recreates `decodeConstructorWords`, and supplies pointwise field refinement.
`codeWP_constructorNonemptyLet_of_capacity` and
`correctConstructorNonemptyReturn_of_capacity` then require only the source
step, generated-operation ABI well-formedness, nonempty/representable layout
bounds, exact address-space capacity, local-write capacity, and the ordinary
continuation induction hypothesis. They construct the concrete heap, address,
host return, witness extension, and target/source agreement internally. The
equation-driven theorem remains internal compatibility factoring; the
contract harness exposes the constructive API. The next allocation task is
to consume `AddressSpaceBudget.consume` in the structural direct-value
induction so sequential allocating paths retain enough headroom. No FIR
semantic contract or executable ABI changed.

W6.6eo establishes the first exact sequential resource transport.
`AddressSpaceBudget.allocateObject` proves that a successful checked object
allocation consumes precisely its aligned header-plus-payload extent.
Specializations for complete UTF-8 String allocation and nonempty constructor
allocation construct the allocation and expose the corresponding residual
budget. The concrete constructor host theorem carries that result through
witness extension and source/runtime refinement.
`codeWP_stringLiteralLet_of_budget` then threads one source-path budget through
the actual compiler/adaptor String prefix and gives the exact remainder to the
arbitrary compiler-selected continuation; the contract harness checks this
certificate-free interface. This is enough to compose sequential String
allocations manually. The general structural theorem still preserves a
single unindexed invariant, so the next slice replaces that resource component
with a before/after indexed law and supplies allocating String and constructor
instances. The resource interface remains deliberately unstable while that
design is completed. No FIR semantic contract or executable ABI changed.

W6.6ep generalizes the structural direct-value theorem to finite allocation.
`DirectValuePathCost` folds an operation cost over the source LCNF `let`
spine. `DirectLetRuntimeRefinesWithCost` is the corresponding before/after
runtime law: a generated direct step consumes the head declaration's cost and
establishes an indexed invariant at the remainder.
`codeWP_of_directValueEvaluates_withCost` proves by source-evaluation
induction that the initial total path cost is enough; compiler and adapter
inversion still recover every target fragment and numeric slot.
`ConcreteBudgetedLocalFrame` combines this address-space index with exact
local-frame shape. Its UTF-8 String instance derives the call, allocation,
witness extension, destination write, and residual budget constructively.
The contract harness now proves arbitrary finite String-literal spines from
one source-computed budget, with no translation certificate or per-node
allocation equation. The next instance is nonempty constructor allocation,
followed by composition with the cost-zero read-only families. The cost and
invariant interfaces remain deliberately unstable. No FIR semantic contract
or executable ABI changed.

W6.6eq adds nonempty constructors to the indexed structural proof.
`NonemptyConstructorSupported` contains only source/compiler layout facts:
the constructor shape, successful argument/result compilation, generated ABI
well-formedness, and representable nonempty counts.
`sourceLetResult_constructor_eq` recovers the exact semantic argument array
and source allocation from ordinary successful source evaluation.
`constructorNonemptyStep_of_budget` combines production argument decoding with
the concrete host theorem and returns the residual `ConstructorLayout` budget
on the resulting store. The indexed runtime-law instance then derives numeric
argument/import/result slots, mixed local/erased physical fields, checked
destination update, witness extension, and source/target agreement.
The contract harness proves arbitrary finite nonempty-constructor spines from
one `DirectValuePathCost`, without per-node concrete steps or a translation
certificate. Cost-zero read-only instances and their union with String and
constructor allocation are next. No FIR semantic contract or executable ABI
changed.

W6.6er proves the first mixed cost-indexed direct fragment.
The local-alias and immediate integer/`USize` runtime laws now have indexed
variants: their generated local operations leave the concrete heap unchanged,
so `directLetAllocationCost = 0` preserves the complete remaining budget.
`BudgetedDirectSupported` composes those families with UTF-8 Strings and
nonempty constructors through `DirectLetRuntimeRefinesWithCost.or`.
The contract harness therefore accepts arbitrary finite interleavings of all
four families from one source-computed path cost. Target instructions, numeric
slots, physical constructor arguments, concrete allocation results, and
per-node budget witnesses are all derived inside the proof. The next slice
lifts the three successful projection families into the same cost-zero
indexed invariant, then turns the structural `CodeWP` into the whole-export
partial-correctness endpoint. No FIR semantic contract or executable ABI
changed.

W6.6es lifts every successful direct projection into the cost-indexed
fragment. Object, `USize`, and packed-integer scalar readers now expose that
their generated concrete operation clears only the host failure slot and
preserves the heap exactly. Their source-facing allocation cost is therefore
zero, and each indexed runtime law returns the full incoming address-space
budget to the continuation. `BudgetedDirectSupported` now admits arbitrary
finite interleavings of aliases, immediate literals, all three successful
projection families, UTF-8 Strings, and nonempty constructors under one
`DirectValuePathCost`. The structural contract harness checks the expanded
union without target instructions, numeric indices, concrete read witnesses,
or per-node budget premises. The next slice packages this structural `CodeWP`
as the whole-export partial-correctness endpoint. No FIR semantic contract or
executable ABI changed.

W6.6et packages the indexed structural proof as a public whole-export
partial-correctness theorem. `ConcreteSupportedExport.correctBudgetedDirect`
takes a successful `DirectValueEvaluates` run through the current mixed
fragment, initial `StateRelated`, exact generated-frame shape, one
source-computed `DirectValuePathCost` budget, and parameter arity. It returns
the executable source observation together with fuel-free termination of the
named concrete Wasm export under `RefinedReturnPost`. The proof internally
applies the production compiler/adaptor equation, the seven-family indexed
runtime law, and the concrete function-body termination bridge. Its public
interface contains no translation certificate, target instruction/index,
concrete operation witness, or per-node allocation premise. This is the first
general whole-export theorem for allocating direct spines; remaining W6 work
extends the admitted syntax/effects and develops the trace/simulation layer
beyond terminating direct evaluation. No FIR semantic contract or executable
ABI changed.

W6.6eu extends that public fragment across all three concrete natural-literal
representations. `naturalAllocationBytes` assigns zero cost to wasm32-tagged
immediates, one aligned object-and-slot extent to source-tagged values that
must be promoted on wasm32, and the aligned limb-object extent to larger
arbitrary-precision naturals. From `FrontierInvariant` and one
`AddressSpaceBudget`, `allocateNatural_eq_ok_of_budget` constructs the
corresponding immediate, promoted, or heap result and returns the exact
residual budget. The indexed compiler law uses that result together with the
existing natural-step simulation, so `NaturalLiteralSupported` joins
`BudgetedDirectSupported` without a caller-supplied allocation equation or
representation witness. The contract harness checks arbitrary finite
Nat-literal spines, including values selected from each representation class;
the existing `correctBudgetedDirect` theorem therefore covers their arbitrary
interleavings with the previously supported direct families unchanged. This
proof-facing cost classification is a workable, deliberately unstable
boundary rather than a compatibility promise. No FIR semantic contract or
executable ABI changed.

W6.6ev opens the indexed structural theorem to real external-call spines.
Lean 4.32 LCNF deliberately has no `Int` literal constructor: source integer
constants are ordinary calls such as `Int.ofNat` and `Int.neg`, so treating
them as another literal family would prove the wrong compiler boundary.
`BudgetedSpineEvaluates` instead interleaves direct source-value steps with
the interpreter's exact three-step external protocol and carries the required
wasm32 budget as a source-execution index. Direct nodes retain
`directLetAllocationCost`; an external node supplies a dynamic Nat cost
because an arbitrary-precision `Nat`, `Int`, or `String` result size may
depend on the actual response. `ExternalLetRuntimeRefinesWithCost` is the
corresponding reusable operation-family law.
`codeWP_of_budgetedSpineEvaluates` inverts the production compiler/adapter and
dispatches to the direct or external law at every node, while
`correctBudgetedSpine` packages the matching executable source observation
(including exact external trace insertion) and fuel-free concrete export
termination. The contract harness confirms that neither interface contains a
target body, numeric Wasm index, concrete response, or per-program simulation
certificate. The next slice instantiates this framework for pure integer
construction calls, starting from constructive heap-Int allocation capacity.
The cost and admission relations remain deliberately unstable. No FIR
semantic contract or executable ABI changed.

W6.6ew supplies that constructive heap-`Int` capacity boundary.
`integerAllocationBytes` computes the current aligned header-plus-magnitude
limb extent directly from the semantic result. From `FrontierInvariant`, one
`AddressSpaceBudget`, and a proof that this exact cost fits,
`allocateInteger_eq_ok_of_budget` constructs the ordinary sign-magnitude
object, derives `UInt32` limb-count encodability from the same wasm32 budget,
writes every limb, and returns the exact residual budget. Callers supply no
allocation equation, encoded count, address, or representation witness. The
contract harness checks this public shape and an executable multi-limb
negative regression checks that the classifier equals the concrete frontier
delta. This is the constructive allocation base for the forthcoming
`Int.ofNat`/`Int.neg` external-family theorem; it does not yet admit those
calls. The classifier and heap layout remain deliberately unstable. No FIR
semantic contract or executable ABI changed.

W6.6ex lifts that capacity result through the executable external-host
boundary. `ConcreteExternalImpl.IntegerResultRefines` states one reusable law
for an entire pair of concrete and semantic handler implementations; it is
not an execution certificate for a compiled program. Given a related request,
the source's canonical integer response, and the exact source-sized budget,
`invoke_pure_integer_result_refines_of_budget` constructs the allocation,
physical address, concrete response, witness extension, related runtime/value,
and exact residual budget. `integerExternalStep_of_budget` then packages the
same result as the Talos host step consumed by generated external-call code.
The contract harness checks that no allocation result, target instruction,
numeric Wasm index, or per-program simulation witness reaches the caller.
The next slice derives the external-call instruction and decoded operands
from the compiler/adapter and instantiates this family for `Int.ofNat` and
`Int.neg`. These proof-facing laws and the heap layout remain deliberately
unstable. No FIR semantic contract or executable ABI changed.

W6.6ey closes the compiler-shaped `Int.ofNat`/`Int.neg` external step.
`PureIntegerExternalSupported` admits exactly those two names and records only
source/compiler facts: the production `compileArgs` result, evaluated source
arguments, exact declaration signature and source response, destination kind,
and response-sized allocation cost. A general decoder theorem turns the
compiler-derived physical operand relation into W6 lanes, while named-call
adapter inversion recovers the numeric declaration call. Whole-export static
alignment now covers external imports as well as runtime imports, connecting
the source declaration metadata and ABI signature to the concrete resolver's
exact host contract.

`externalLetRuntimeRefinesWithCost_pureInteger` composes those facts with the
reusable `IntegerResultRefines` implementation law. It internally constructs
the physical operands, import/local indices, request relation, allocation and
address, concrete response, extended witness, destination write, exact
source-trace runtime, Talos WP, and residual budget. The contract harness
checks that none of those target or allocation witnesses appear in the public
interface. The implementation law is threaded as an installed-host invariant
because `StateRelated` deliberately ignores host configuration. The next
slice lifts the existing direct-operation laws through that invariant so
arbitrary direct and pure-Int steps can use `correctBudgetedSpine` together.
These proof-facing admission and layout surfaces remain deliberately
unstable. No FIR semantic contract or executable ABI changed.

W6.6ez closes that mixed-spine composition boundary.
`DirectLetRuntimeRefinesWithCost` now requires every admitted direct helper to
preserve the installed `Host.externals` field as well as the semantic state,
local frame, and exact residual budget. The eight current direct families
discharge the stronger law from their concrete `targetStore`,
`clearFailure`, or `replaceHeap` result. A generic
`preservingExternalInvariant` theorem then lifts any such direct family
through a property of the installed concrete implementation.

`directLetRuntimeRefines_budgetedDirect_integerExternal` applies that lift to
`IntegerResultRefines`, and
`correctBudgetedIntegerExternalSpine` combines it with the compiler-shaped
external theorem. The resulting public theorem accepts an arbitrary finite
source evaluation interleaving the full current direct family with
`Int.ofNat`/`Int.neg`, one exact path budget, and the initially installed
integer-handler family law. It derives all target steps and returns exact
source execution plus fuel-free named-export termination; callers provide no
runtime-law arguments or per-node target witnesses. The next external slice
can enlarge the source-facing integer operation family without changing this
structural theorem. These proof-facing laws remain deliberately unstable. No
FIR semantic contract or executable ABI changed.

W6.6fa performs that first family extension. The new
`PureIntegerExternalName` relation makes the source-facing gate explicit and
admits `Int.ofNat`, `Int.neg`, `Int.add`, and `Int.sub`. The generic
compiler/adapter/resolver proof remains name-agnostic: successful source
evaluation fixes the exact canonical integer response and cost, while the
installed `IntegerResultRefines` law constructs the concrete allocation and
related result. Consequently the existing
`correctBudgetedIntegerExternalSpine` theorem now covers construction and
binary arithmetic calls without any new target witness or structural proof.
The contract harness checks all four name constructors. The next external
family boundary is the distinct result representation used by operations such
as `Int.natAbs` or `Int.decLt`; it should not be folded into the integer-result
law. These proof-facing gates remain deliberately unstable. No FIR semantic
contract or executable ABI changed.

W6.6fb adds the distinct representation-polymorphic natural-result family.
`semanticNaturalExternalResponse` reuses the source interpreter's `literal`
transition, while `concreteNaturalExternalResponse` carries the exact word
returned by `allocateNatural`. The unified allocation refinement constructs an
existential post-witness across all three cases: unchanged for an immediate,
descriptor-extended for a promoted source tag, and location-extended for a
limb object. `NaturalResultRefines`,
`invoke_pure_natural_result_refines_of_budget`, and
`naturalExternalStep_of_budget` lift that boundary through exact pure-event
traces and the Talos host step without a representation certificate.

`PureNaturalExternalName` initially admits `Int.natAbs`.
`externalLetRuntimeRefinesWithCost_pureNatural` reconstructs its production
argument prefix, external import, request relation, result representation,
destination write, and residual budget. The installed handler law is threaded
through the current direct family, and
`correctBudgetedNaturalExternalSpine` closes arbitrary finite direct/`natAbs`
interleavings at the named-export boundary. `Int.decLt` remains a separate
nonallocating scalar-result family. These proof-facing response, cost, and
admission surfaces are deliberately unstable. No FIR semantic contract or
executable ABI changed.

W6.6fc adds the nonallocating scalar-result family.
`concreteScalarExternalResponse` and `semanticScalarExternalResponse` reuse
`BoxedScalar` as an ABI-indexed lane vocabulary without allocating a box.
`ScalarResultRefines` preserves the heap and witness exactly, and
`scalarExternalStep` derives the related Talos return and exact event trace.
`PureScalarExternalName` initially admits `Int.decLt` only at `.uint8`;
`externalLetRuntimeRefinesWithCost_pureScalar` reconstructs its production
compiler, adapter, resolver, operand, and destination facts at zero allocation
cost. `correctBudgetedScalarExternalSpine` closes arbitrary finite
direct/`Int.decLt` spines. The generic runtime law may support more scalar
names later, but admission remains explicit and deliberately unstable. No FIR
semantic contract or executable ABI changed.

W6.6fd composes the three proved pure-result families under one structural
invariant. `ExternalLetRuntimeRefinesWithCost` now records preservation of the
installed concrete handler table; generic disjunction, invariant-extension,
and invariant-transport laws use that fact to retain `IntegerResultRefines`,
`NaturalResultRefines`, and `ScalarResultRefines` simultaneously.
`PureExternalSupported` is the source-facing union, and
`externalLetRuntimeRefinesWithCost_pureExternal` supplies its uniform runtime
law. The matching direct law retains the same combined frame.

`correctBudgetedPureExternalSpine` therefore proves one arbitrary finite
source spine that freely interleaves the complete current direct family,
`Int.ofNat`/`Int.neg`/`Int.add`/`Int.sub`, `Int.natAbs`, and `Int.decLt`.
Its caller supplies source evaluation, one exact path budget, and the three
installed operation-family laws once; compiler code, numeric indices,
concrete result representations, target steps, and witness extensions remain
internal. The contract harness checks both the compositional runtime law and
the whole-export application. These proof-facing admission and invariant
surfaces are deliberately unstable. No FIR semantic contract or executable
ABI changed.

W6.6fe aligns that certificate-free theorem with the remaining resident
numeric helpers generated by W7. `PureNaturalExternalName` now admits
`Nat.add` and `Nat.sub` alongside `Int.natAbs`;
`PureScalarExternalName` admits `Nat.decEq`, `Nat.decLt`, and `Nat.decLe`
alongside `Int.decLt`, all at the exact `.uint8` result kind. The
name-agnostic natural/scalar compiler and runtime theorems require no changes:
the successful semantic response still determines the concrete
representation, residual budget, exact trace, and destination write.
Consequently `correctBudgetedPureExternalSpine` now covers all ten declarations
in W7's current `ResidentNumeric.externalDeclarations` surface. The contract
harness checks every new name/kind constructor. No FIR semantic contract,
concrete layout, or executable ABI changed.

W6.6ff opens certificate-free control flow. `BudgetedCodeEvaluates` extends
the exact finite source relation with selected case nodes at unchanged heap
cost. `CaseRuntimeRefines` is the corresponding reusable theorem condition:
for every successful production compiler/adapter output, it recovers the
selected target and lifts a `CodeWP` for that branch through the generated
case dispatcher. `codeWP_of_budgetedCodeEvaluates` and
`ConcreteSupportedExport.correctBudgetedCode` compose this law structurally
with the existing direct and external family laws.

The first constructive instance is deliberately small but fully nested.
`DefaultOnlyCaseSupported` admits a sole default alternative;
`caseRuntimeRefines_defaultOnly` proves that production compilation erases
the wrapper to the selected branch, and
`correctBudgetedPureExternalDefaultCases` closes arbitrary nesting of those
cases around all current direct operations and all ten resident numeric
externals. The contract harness checks the generic case law and the
whole-export application. No caller supplies compiled target code, numeric
indices, or a translation certificate. The next control-flow slices are
constructor-tag and scalar case chains using the concrete `getTag` and scalar
comparison rules. These proof-facing admission surfaces remain deliberately
unstable. No FIR semantic contract, concrete layout, or executable ABI
changed.

W6.6fg closes the first real certificate-free dispatcher. The earlier
unrestricted selected-branch transformer was stronger than generated Wasm
control flow requires: an `if` arm installs a resumption wrapper for
fallthrough and breaks. `CaseResumptionStable` now states that exact semantic
condition. The mixed syntax induction proves
`ExactReturnControlPost` internally—an explicit Wasm return, which is stable
under arm resumption—and weakens it to `ConcreteFunctionBodyPost` only after
the complete body proof has been assembled.

Case admission is now indexed by the current source runtime and environment.
This permits `SingleObjectConstructorCaseSupported` to state the one dynamic
fact needed by the concrete i32 tag test: every successfully selected
semantic tag fits `UInt32`, without exposing physical words, numeric locals,
import indices, or target instructions. Production inversion
`singleObjectConstructorCases_eq` derives the selected target, discriminator
index, `getTag` import, and exact singleton test. Resolver alignment,
`StateRelated`, and `caseChainWP_constructor` then prove
`caseRuntimeRefines_singleObjectConstructor`.
`correctBudgetedPureExternalSingleObjectConstructorCases` consequently closes
arbitrary nesting of singleton constructor hits around all current direct
operations and ten resident numeric externals. The contract harness checks
the stable-post law, runtime instance, and whole-export application. Multi-arm
hit/miss/default and scalar comparison chains are next. These proof-facing
surfaces remain deliberately unstable. No FIR semantic contract, concrete
layout, executable ABI, or W7 helper signature changed.

W6.6fh closes the first ordered multi-arm dispatcher. Production inversion
`twoObjectConstructorDefaultCases_eq` derives all three adapted branches, the
shared discriminator/import indices, and the exact nested target for two
object-constructor arms followed by a default.
`TwoObjectConstructorDefaultCasesSupported` remains source/runtime-facing: it
records that source shape, object-tag compilation, both static tag bounds, and
the semantic actual-tag bound, but no target evidence.
`caseRuntimeRefines_twoObjectConstructorDefault` proves first-arm hit,
second-arm hit after one miss, and default selection after two misses against
the concrete `getTag` host. `CaseResumptionStable.resume` supplies the precise
closure fact needed by the nested generated `if` wrappers.
`correctBudgetedPureExternalTwoObjectConstructorDefaultCases` lifts the result
to arbitrary nesting around all current direct operations and ten resident
numeric externals. The contract harness checks the nested stability law,
runtime instance, and whole-export application. General-length constructor
chains and scalar `UInt8` comparisons are next. No FIR semantic contract,
concrete layout, executable ABI, or W7 helper signature changed.

W6.6fi removes the constructor-chain arity bound. Generic inverse theorems now
recover the public fallback compiler result and constructor-chain result from
successful recursive-core execution. `CodeAdapted.cases_eq` exposes the actual
fallback and adapted chain for every production-compiled case, while
`CaseChainAdapted.objectConstructor_eq` peels one generated object-tag test
without accepting a target description.

`ObjectConstructorCaseAltsSupported` admits any normalized constructor-only
list or constructor list with exactly one trailing default; every expected tag
must fit the i32 discriminator lane. `ObjectConstructorCasesSupported` adds
only object-tag compilation, discriminator-local compilation, and the semantic
actual-tag bound. Its recursive theorem
`objectConstructorCaseChainRefines` follows `chooseAlt`: a hit consumes the
selected branch proof, and a miss recurses through the production suffix under
`CaseResumptionStable.resume`.
`caseRuntimeRefines_objectConstructorCases` and
`correctBudgetedPureExternalObjectConstructorCases` consequently close
arbitrary-length object-constructor dispatch and arbitrary nesting around the
current direct/resident-numeric family. The singleton and two-arm theorems
remain compatibility surfaces. The contract harness checks generic compiler
inversion, runtime refinement, and whole-export use. Scalar `UInt8` comparison
chains are next. No FIR semantic contract, concrete layout, executable ABI, or
W7 helper signature changed.

W6.6fj closes that scalar control-flow family at the same arbitrary-chain
boundary. `CaseChainAdapted.scalarUInt8Constructor_eq` peels one production
local/constant comparison and its recursively compiled suffix.
`ScalarUInt8CaseAltsSupported` admits any normalized constructor-only list or
constructor list with exactly one trailing default, with every expected tag
inside the compiler's `UInt8` lane. `ScalarUInt8CasesSupported` adds only the
scalar discriminator mode and compiler local-kind equation; the semantic
actual-tag bound is derived constructively from `StateRelated` and
`ValueRel.uint8`.

`caseChainWP_scalarUInt8_constructor` proves the exact direct Wasm comparison
without a host import. `scalarUInt8CaseChainRefines` follows the
source-selected hit/miss path under nested case-resumption wrappers, and
`caseRuntimeRefines_scalarUInt8Cases` supplies the reusable runtime condition.
`correctBudgetedPureExternalScalarUInt8Cases` consequently closes arbitrary
chain length and arbitrary nesting around the current direct/resident-numeric
family. The contract harness checks both the generic runtime law and
whole-export endpoint. No FIR semantic contract, concrete layout, executable
ABI, or W7 helper signature changed.

W6.6fk extends the same certificate-free structural induction through
successful no-result effect nodes. `EffectSupportedPredicate` records only
the source code, continuation, and next runtime, while
`EffectRuntimeRefines` is the uniform operation-family condition over every
successful production compiler/adapter output. The generic
`codeWP_of_budgetedCodeEvaluates` theorem now composes direct, external, case,
and effect laws without embedding a target witness in source evaluation.

The first constructive effect instance is compiler-erased persistent
ownership. `PersistentOwnershipEffectSupported` admits persistent increments
and decrements whose source continuation keeps the same runtime. Production
inversions `CodeAdapted.incPersistent_eq` and
`CodeAdapted.decPersistent_eq` recover the adapted continuation, and
`effectRuntimeRefines_persistentOwnership` proves both operations are exact
source/concrete no-ops for every invariant. Consequently
`correctBudgetedPureExternalPersistentOwnership` closes arbitrary
interleavings of those effects, default-only cases, the current direct
family, and all ten resident numeric externals. Persistent operations consume
zero heap budget and preserve world, trace, concrete heap, locals, witness,
and installed external laws exactly. The contract harness checks the generic
effect law and whole-export endpoint. The proof-facing admission surface is
deliberately unstable. No FIR semantic contract, concrete layout, executable
ABI, or W7 helper signature changed.

W6.6fl closes the first generated-host-call effect family under that generic
condition. `OrdinaryIncrementEffectSupported` admits a successful
nonpersistent increment using only its semantic lookup/update, source-local
ABI kind, and wasm32 reference-count headroom. `CodeAdapted.inc_eq` inverts
the production compiler and adapter to recover the numeric object/import
slots and independently adapted continuation.
`ConcreteSupportedExport.incrementCall` derives the executable increment
contract from whole-module resolver alignment.

The underlying concrete increment refinement now exposes its exact
heap-frontier preservation in addition to mapped-allocation capacity.
`effectRuntimeRefines_ordinaryIncrement` composes those facts into the
complete budgeted pure-external frame: the generated unary host call changes
the related ownership header and semantic runtime while preserving allocation
budget, locals, witness, handler table, world, and trace according to their
existing relations. `correctBudgetedPureExternalOrdinaryIncrements`
therefore closes arbitrary interleavings of successful ordinary increments,
default-only cases, all current direct operations, and the ten resident
numeric externals. The contract harness checks the reusable effect law and
whole-export endpoint. No target instructions, numeric indices, concrete
addresses, or per-program simulation certificates cross the public boundary.
No FIR semantic contract, concrete layout, executable ABI, or W7 helper
signature changed.

W6.6fm closes ordinary recursive decrement under the certificate-free effect
condition. A general executable theorem proves that successful
`decrementReferenceOnceFuel`, its public one-step wrapper, and arbitrary
multi-decrement folds preserve `heapCursor` exactly: recursive release consists
only of header rewrites and folds of the same cursor-preserving operation.
The existing heap/runtime/effect refinement boundaries now export that exact
frontier fact alongside mapped-header capacity.

`OrdinaryDecrementEffectSupported` retains only the semantic lookup/update and
the source local's ABI kind. `CodeAdapted.dec_eq` and resolver alignment derive
the numeric local/import slots, exact `dec` contract, and adapted continuation.
Recursive closure release needs immutable host/witness descriptor agreement,
so `ConcreteBudgetedPureExternalOwnershipFrame` threads that relation as
proof-side state instead of adding it to source admission. Costed direct and
external runtime laws now expose independent preservation of both descriptor
tables, and reusable lifting theorems re-establish their agreement after every
surrounding node.

`effectRuntimeRefines_ordinaryDecrement` proves the generated unary host call
at zero allocation cost, and
`correctBudgetedPureExternalOrdinaryDecrements` closes arbitrary successful
decrements interleaved with default-only cases, all current direct operations,
and the ten resident numeric externals. The contract harness checks both
boundaries. This is a proof-surface extension only: no FIR semantic contract,
concrete layout, executable ABI, or W7 helper signature changed.

W6.6fn adds successful explicit deletion to the same structural proof. The
concrete erased-token and ordinary live-object refinement branches now expose
exact `heapCursor` preservation through `deleteStep` and the generated effect
simulation. `OrdinaryDeleteEffectSupported` contains only the source lookup,
successful semantic deletion, and source-local compiler equation; it does not
admit a physical word, target index, or per-node translation witness.

`CodeAdapted.del_eq` reconstructs the numeric object/import slots and adapted
continuation from the production compiler and adapter.
`ConcreteSupportedExport.deleteCall` supplies the exact resolver-installed
unary contract. `effectRuntimeRefines_ordinaryDelete` then preserves the
complete budgeted pure-external frame at zero allocation cost for both the
ordinary canonical-header release and the exact erased/physical-zero no-op.
`correctBudgetedPureExternalOrdinaryDeletes` packages arbitrary successful
deletions interleaved with default-only cases, all current direct operations,
and the ten resident numeric externals. The contract harness checks the
operation-family law and whole-export endpoint. No FIR semantic contract,
concrete layout, executable ABI, or W7 helper signature changed.

W6.6fo removes the artificial one-effect-family boundary. The generic
`EffectSupportedOr` admission contains only one of two source-family
derivations, and `EffectRuntimeRefines.or` proves that any two uniform runtime
laws preserving the same invariant compose. `OwnershipEffectSupported` uses
that binary union to admit compiler-erased persistent increment/decrement,
ordinary increment, recursive decrement, and explicit deletion in one source
evaluation.

Increment and deletion now also have ownership-frame specializations. Their
concrete heap-only transitions preserve the host/witness closure-descriptor
agreement needed by a later recursive decrement. The combined
`effectRuntimeRefines_ownership` theorem is assembled from the four reusable
operation laws with the general union theorem.
`correctBudgetedPureExternalOwnership` consequently permits arbitrary
interleavings of all four ownership families with default-only cases, all
current direct operations, and the ten resident numeric externals. The only
additional entry invariant is descriptor-table agreement; there are no
operation-specific target witnesses or runtime-law premises at the whole-
export boundary. No FIR semantic contract, concrete layout, executable ABI,
or W7 helper signature changed.

W6.6fp extends that compositional endpoint with successful constructor-tag
mutation. The concrete `writeTag` refinement, Talos step, and generated effect
simulation now expose exact `heapCursor` preservation in addition to retained
mapped-header capacity. `ConstructorTagEffectSupported` records only the
object-local compiler equation, semantic lookup/update, live-constructor
facts, and wasm32 tag bound; it contains no target program, numeric index,
concrete address, or simulation witness.

`CodeAdapted.setTag_eq` reconstructs the generated unary prefix and adapted
continuation from production compilation. `ConcreteSupportedExport.setTagCall`
derives the resolver-installed concrete contract.
`effectRuntimeRefines_constructorTag` threads the ownership-aware budget,
installed pure-external laws, and closure-descriptor agreement through the
heap-only header mutation. The general union theorem then yields
`effectRuntimeRefines_ownershipAndTag`, and
`correctBudgetedPureExternalOwnershipAndTag` permits arbitrary interleavings
of all proved ownership effects and tag mutations around default-only cases,
the current direct family, and ten resident numeric externals. The contract
harness checks both reusable laws and the whole-export endpoint. No FIR
semantic contract, concrete layout, executable ABI, or W7 helper signature
changed.

W6.6fq adds successful FVar object-field mutation as the next compositional
effect family. `writeObjectField_refines_with_capacity`, the Talos operation
step, and the generated effect simulation now expose exact `heapCursor`
preservation from their existing target-mutation frame.
`ObjectFieldFVarEffectSupported` contains only semantic lookup/update and
live-constructor facts, source-local compiler equations, the object-field kind
gate, bounds, and one universally quantified source typing premise connecting
the selected constructor slot to the compiler-selected field kind. It chooses
no witness, physical word, descriptor, numeric index, target program, or
simulation derivation.

`CodeAdapted.objectSetFVar_eq` derives both numeric locals, the object-set
import, exact binary prefix, and continuation from production output.
`ConcreteSupportedExport.objectSetCall` supplies the resolver-installed
contract. The runtime law recovers the physical object and constructor
descriptor from `StateRelated` and the successful semantic constructor decode;
the source typing premise supplies only slot-kind agreement.
`effectRuntimeRefines_objectFieldFVar` preserves the ownership-aware budget,
installed pure-external laws, and descriptor-table agreement.
`effectRuntimeRefines_ownershipTagAndObjectFVar` and
`correctBudgetedPureExternalOwnershipTagAndObjectFVar` extend the mixed
endpoint accordingly. The erased object-field argument retains its existing
operation theorem and is the next production constant-prefix inversion slice.
No FIR semantic contract, concrete layout, executable ABI, or W7 helper
signature changed.

W6.6fr closes that remaining erased object-field branch.
`instructions_localGet_erased_call_eq` inverts the exact adapted
`local.get; i32.const 0; call` prefix, and
`CodeAdapted.objectSetErased_eq` derives it from the production compiler
together with the independently adapted continuation.
`ObjectFieldErasedEffectSupported` contains only the semantic lookup/update,
live-constructor and bounds facts, the source-local compiler equation, and a
universally quantified source typing premise identifying the selected
descriptor slot as erased. It admits no numeric local/import slot, target
program, concrete word, descriptor, witness, or execution certificate.

`effectRuntimeRefines_objectFieldErased` reconstructs those concrete facts
from production output and `StateRelated`, then consumes the existing
cursor-preserving erased object-set theorem.
`ObjectFieldEffectSupported` and `effectRuntimeRefines_objectField` combine
the FVar and erased forms, while
`OwnershipTagAndObjectEffectSupported`,
`effectRuntimeRefines_ownershipTagAndObject`, and
`correctBudgetedPureExternalOwnershipTagAndObject` extend the mixed
whole-export theorem across every `LCNF.Arg` form accepted by `objectSet`.
Compatibility theorems for the earlier FVar-only boundary remain available.
No FIR semantic contract, concrete layout, executable ABI, or W7 helper
signature changed.

W6.6fs lifts successful `USize` field mutation through the same structural
boundary. The concrete `writeUSizeField`/`writeUSizeSlot`, Talos operation, and
generated effect theorems now expose exact `heapCursor` preservation from
their existing payload-mutation frame. `CodeAdapted.usizeSet_eq` recovers both
numeric locals, the `usizeSet` import, exact binary prefix, and continuation
from production output; `ConcreteSupportedExport.usizeSetCall` recovers the
installed concrete contract.

`USizeFieldEffectSupported` admits only source lookups/update, live-constructor
bounds, and the two source-local compiler equations. It contains no target
syntax, numeric index, physical value, witness, or simulation proof.
`effectRuntimeRefines_usizeField` reconstructs those facts and preserves the
ownership-aware budget and descriptor agreement.
`FieldMutationEffectSupported`,
`effectRuntimeRefines_fieldMutation`,
`OwnershipTagAndFieldMutationEffectSupported`, and
`correctBudgetedPureExternalOwnershipTagAndFieldMutation` extend the mixed
whole-export endpoint across object and `USize` mutation. Packed-scalar
mutation is the next adjacent successful field family. No FIR semantic
contract, concrete layout, executable ABI, or W7 helper signature changed.

W6.6ft completes successful constructor-field mutation for every packed
integer width implemented by the concrete resolver. The four concrete
`writeScalarUInt*Field`, Talos operation, and generic effect theorems now
expose exact `heapCursor` preservation from their existing whole-heap frames.
`CodeAdapted.scalarSet_eq` derives both numeric locals, the kind-indexed
`scalarSet` call, exact binary prefix, and continuation from production
compiler/adaptor output. A narrow public resolver theorem exposes that the
four packed integer kinds select `scalarSetFn` without exposing the private
kind classifier; `ConcreteSupportedExport.scalarSetCall` then recovers the
installed concrete contract.

`ScalarFieldEffectSupported` contains source lookups/update, live-constructor
facts, the two source-local compiler equations, and a universal
compiler-shaped layout judgment. The judgment proves retained-field
separation, the `size + usize` scalar coordinate, and width-specific `ssize`
fit. It carries no numeric target slot, target syntax, physical word,
descriptor, witness, or simulation certificate.
`effectRuntimeRefines_scalarField` reconstructs all concrete evidence from
production output and `StateRelated`; its four supported width cases preserve
the ownership-aware address-space budget and descriptor agreement.
`AllFieldMutationEffectSupported`,
`OwnershipTagAndAllFieldMutationEffectSupported`, and
`correctBudgetedPureExternalOwnershipTagAndAllFieldMutation` extend the mixed
whole-export endpoint across object, `USize`, and packed-integer writes.
Floating-point scalar setters remain outside the concrete resolver/runtime
fragment. No FIR semantic contract, concrete layout, executable ABI, or W7
helper signature changed.

W6.6fu adds successful `isShared` observations to the certificate-free
budgeted direct family. `IsSharedSupported` retains only the source
declaration, compiler-selected object/result kinds, local compiler equations,
and the target-independent `.tobject` refinement fact. It carries no numeric
local/import, concrete word, target syntax, runtime read, or simulation
certificate.

The source-step inversion proves that every successful observation is a
direct `UInt8`; production lowering/adaptation recovers the exact
`local.get; call` prefix, and `ConcreteSupportedExport.isSharedCall` recovers
the installed unary concrete contract. `StateRelated` supplies the tagged,
promoted, or ordinary heap representation consumed by the existing
`isSharedStep_of_refines` theorem.
`directLetRuntimeRefinesWithCost_isShared` then writes the generated result
local and preserves the heap frontier, address-space budget, installed
external implementation, and both closure-descriptor tables. Extending
`BudgetedDirectSupported` makes `isShared` available immediately in every
existing mixed whole-export theorem. No FIR semantic contract, concrete
layout, executable ABI, or W7 helper signature changed.

W6.6fv adds successful typed unboxing to the same certificate-free budgeted
direct family. `SourceUnboxKindCompatible` states the genuinely necessary
source condition: tagged objects are representation-polymorphic, while a
live semantic heap box must contain a scalar whose constructor agrees with
the compiler-selected one of the five supported integer/`USize` result kinds.
`UnboxSupported` combines that source judgment with the declaration type and
source-local compiler equations. It contains no concrete word, descriptor
lookup, checked memory read, numeric target slot, target syntax, or execution
certificate.

`ConcreteRuntimeRel.unboxFacts_of_sourceCompatible` derives the tagged or heap
`UnboxObjectRel`, frozen heap descriptor, checked `readBoxedScalar`, and exact
semantic result from the ordinary state relation. Production lowering and
adaptation recover the unary `local.get; call` prefix;
`ConcreteSupportedExport.unboxCall` recovers the installed typed concrete
contract through a narrow public resolver theorem.
`directLetRuntimeRefinesWithCost_unbox` composes those facts with the existing
generated unbox step, exact i32/i64 destination write, arbitrary continuation,
and unchanged heap/budget/metadata frame. Extending `BudgetedDirectSupported`
makes compatible unboxing available in every existing mixed whole-export
theorem. The source compatibility premise is necessary because FIR heap
unboxing deliberately ignores its stored type annotation; without it, a
program can box one scalar width and request another. No FIR semantic
contract, concrete layout, executable ABI, or W7 helper signature changed.

W6.6fw adds successful integer boxing to that certificate-free direct family.
`BoxSupported` records only the source box annotation and the compiler-local
operand/result kind equations for one of the five supported integer/`USize`
kinds. The scalar value, physical lane, numeric local/import indices,
allocation result, and target step are all reconstructed internally.

`boxScalarAllocationBytes` is a fixed aligned header-plus-slot reservation.
Both allocating representations—promoted source tags and ordinary heap
boxes—use exactly that extent; wasm32 immediates allocate nothing and use the
general `AddressSpaceBudget.weaken` rule to establish the conservative
residual proof index. `boxScalar_eq_ok_of_budget` makes all three branches
constructive. Production compiler/adaptor inversion, `StateRelated`,
`ConcreteSupportedExport.boxCall`, and the existing generated box-step theorem
then prove `directLetRuntimeRefinesWithCost_box`. Source-step determinism
identifies the constructed semantic result with the interpreter result.
Extending `BudgetedDirectSupported` makes boxing available in every existing
mixed whole-export theorem without a per-program certificate. This changes
no FIR semantic contract, concrete layout, executable ABI, or W7 helper
signature.

W6.6fx replaces reset's earlier branch-specific composition surface with a
certificate-free structural theorem. `ResetSupported` records only the source
declaration, object/result local compiler equations, and ordinary `.tobject`
typing. It contains no tagged/fallback/unique choice, concrete object word,
heap cell, reset token, target index, capacity witness, or execution step.

`resetStep_of_refines` derives all three successful branches from the
successful semantic reset and `ConcreteRuntimeRel`. The fallback theorem now
covers both persistent and nonunique objects, while unique constructor reset
retains its exact witness rebind and mapped-header transport. Every successful
branch proves exact heap-frontier preservation and unchanged witness closure
descriptors. Production lowering/adaptation and
`ConcreteSupportedExport.resetCall` recover the generated unary call;
`directLetRuntimeRefinesWithCost_reset` performs the reuse-token local write
and re-establishes the complete pure-external ownership frame at zero cost.
`OwnershipBudgetedDirectSupported` keeps reset separate from the ordinary
direct family because recursive capture release needs descriptor agreement,
then composes both laws. The strongest ownership/tag/all-field-mutation
whole-export endpoint now admits arbitrary interleaving of successful reset
without a per-program or branch certificate. No FIR semantic contract,
concrete layout, executable ABI, or W7 helper signature changed.

W6.6fy closes the corresponding branch-independent *operation* boundary for
successful reuse. `reuseStep_of_capacityEvidence` consumes the authoritative
static fitting-capacity result and its dynamic `ReuseCapacityValueRel`, then
derives whether the runtime token is zero or names a retained allocation. It
selects fresh tagged allocation, fresh heap allocation, or checked in-place
reuse internally and returns the exact `afterReuse` fact, witness transport,
runtime/value refinement, closure-descriptor preservation, and retained-header
transport. The theorem contains no target instruction sequence, numeric
import/local index, or per-program simulation certificate.

This slice also corrects the dynamic retained-evidence relation: a retained
object may be represented by a tagged result because the retained claim
constrains only a later *nonzero* reset token. The missing case is recorded and
closed by `FIR-BUG-wasm-none-reuse-retained-zero-empty-result`.

W6.6fz lifts that operation boundary through the production compiler and
adapter. `ReuseSupported` is target-free: it records the source declaration,
compiler equations, authoritative fitting-capacity result, result
compatibility, and wasm32 bounds. `reuseLetStep_of_capacity` reconstructs the
mixed token-local plus local/erased-field prefix, runtime import, physical
arguments, result local, and concrete execution. A new
`constructorAllocationBytes` boundary and
`allocateConstructor_eq_ok_of_budget` construct immediate, promoted, or heap
allocation from one representation-sensitive reservation, so the zero-token
branch no longer assumes a successful `reuseObject`. The theorem returns the
exact `reuseCapacityLetFacts?` successor and its complete dynamic state
relation; it exposes no target index, token word, allocation result,
representation branch, or simulation certificate.

Two coordinated shared-validator obligations now delimit the structural
whole-export endpoint. A retained token must remain tied to an ordinary source
cell across intervening effects; the current fact transfer can preserve it
after an alias makes the cell persistent, as recorded by
`FIR-BUG-wasm-none-reuse-retained-token-ordinary`. Also, retained provenance is
representation-polymorphic for an empty replacement: the zero branch returns
a tagged object and the nonzero branch returns a heap address, so the result
ABI kind must be `.tobject`. The current validator does not combine provenance
with result kind; this gap remains
`FIR-BUG-wasm-none-reuse-retained-result-kind`. The compiler theorem keeps
these two semantic obligations explicit rather than weakening the concrete
runtime relation.

W6.6ga turns the successful production reuse theorem into a complete
fact-indexed resource step. Nonzero `reuseObject` preserves `heapCursor`, and
the generic cursor transport rule consequently preserves any weakened
address-space budget; the zero branch returns the exact
`constructorAllocationBytes` remainder. On the source side, successful reuse
preserves the persistence bit of every pre-existing ordinary cell, creates
only ordinary fresh cells, and always returns an object rather than another
reuse token. Therefore `ReuseTokenOrdinaryRel.bindReuse` transports every old
retained-token obligation through the authoritative result-fact insertion,
including aliases of the rewritten cell and previously dangling locations
that coincide with a fresh allocation. `reuseLetStep_of_capacity` now returns
the next fact relation, next ordinary-token relation, next local-frame
alignment, and exact residual budget together. The ordinary-token bug is
accordingly limited to unrelated intervening effects whose shared fact
transfer fails to invalidate a retained token; successful reuse itself no
longer loses the invariant. The provenance-sensitive `.tobject` gate remains
the other coordinated validator obligation.

W6.6gb packages that step as a certificate-free facts-indexed structural
proof. `ReuseCapacityDirectLetRuntimeRefinesWithCost` universally quantifies
production compiler and adapter outputs and advances
`ConcreteReuseCapacityFrame`; `ReuseCapacityCodeEvaluates` records only source
steps, source admission, exact path cost, and the authoritative validator fact
equation. Structural induction yields
`codeWP_of_reuseCapacityCodeEvaluates_exactReturn`, its function-body form, and
`correctReuseCapacityCode`: for any finite successful reuse-only source spine,
the source reaches its returned observation and the actual generated export
terminates with a refined return. No target program, numeric index, concrete
word, allocation/branch witness, or per-program translation derivation is a
premise. This is the first pragmatic finite theorem for the facts-indexed
reuse path; the same uniform step law is retained for the later trace-based
simulation/bisimulation layer. Mixed effects still require the two shared
validator fixes above.

W6.6gc states the exact semantic condition for safe mixed composition.
`OrdinaryPersistenceTransport` says that every cell visible after an
unrelated source step is ordinary whenever all matching pre-step cells were
ordinary; the formulation also requires newly introduced cells to be
ordinary. The relation is reflexive and transitive, and
`ReuseTokenOrdinaryRel.eraseBind` uses it to preserve all non-shadowed token
facts. The facts-indexed runtime law and all three structural/export theorems
are now operation-family generic. Their first disjunctive instance,
`ReuseAliasSupported`, combines successful validated reuse with arbitrary
cost-zero local aliases, and `correctReuseAliasCode` proves the resulting
finite generated export without a target certificate. Further direct and
effect families join by proving this same source transport plus the already
isolated witness/header-capacity transport.

W6.6gd widens that first mixed endpoint to the heap-preserving literal and
projection core. Immediate integer/`USize` literals and successful `USize`,
object, and packed-scalar projections each preserve the facts relation,
ordinary-token relation, exact local frame, and address-space budget while
deriving their production compiler/adapter code. `ReuseReadOnlySupported`
composes those laws with reuse and aliases; `correctReuseReadOnlyCode` proves
arbitrary finite interleavings through the actual generated export.

W6.6ge opens that allocating boundary with nonempty constructors.
`OrdinaryPersistenceTransport` is now reflexive, transitive, and instantiated
for fresh ordinary allocation, `allocCtor`, and reuse.
`ReuseTokenOrdinaryRel.bindObject` packages the common rule that an
object-valued result makes its inserted fact vacuous as a token while every
old fact crosses the source transport. The budgeted nonempty-constructor
runtime theorem now also exposes its exact `ReuseCapacityValueRel` result and
mapped-header transport. The facts-indexed production law consumes those
facts to insert the validator-selected constructor bound, and
`correctReuseReadOnlyConstructorCode` proves arbitrary finite interleavings
of reuse, the read-only direct family, and nonempty allocation. Natural,
String, and boxed ordinary results are the next allocating families.

W6.6gf closes the remaining heap-preserving direct readers. Successful typed
unboxing and `isShared` now instantiate the same facts-indexed law: both erase
only the destination fact, preserve every older header-capacity fact, carry
ordinary-token provenance by reflexive source transport, and consume zero
address-space budget. `ReuseReadOnlySupported` and therefore
`correctReuseReadOnlyConstructorCode` now include these representation- and
ownership-sensitive observations. The next widening step remains Natural,
String, and boxed ordinary allocation.

W6.6gg adds integer boxing across all three physical representations.
`box_ordinaryPersistenceTransport` proves that semantic boxing either leaves
the source heap unchanged or appends one fresh ordinary box.
`HeaderCapacityTransport.boxScalar` already gives the matching concrete
retained-header transport for immediate, promoted-tag, and heap-box results.
The facts-indexed production law now composes those transports with the exact
one-slot reservation, witness extension, destination-fact erasure, and
generated export. `correctReuseConstructorBoxCode` covers arbitrary finite
interleavings of boxing with reuse, every heap-preserving direct reader, and
nonempty constructors. Natural and String literals are the remaining direct
allocating families in this fragment.

W6.6gh closes those remaining direct allocating families. One generic
`literal_ordinaryPersistenceTransport` covers heap identity for immediate
literals, the tagged/fresh split for Naturals, and fresh ordinary String
allocation. The Natural and String facts-indexed production laws combine it
with their existing witness extension, retained-header transport, exact
source-derived allocation cost, and generated calls.
`ReuseBudgetedDirectSupported` is now precisely the current
`BudgetedDirectSupported` family plus validated reuse, and
`correctReuseBudgetedDirectCode` proves finite whole-export partial
correctness for arbitrary interleavings of that complete direct fragment.
The next widening frontier is the ownership/effect family rather than another
direct-result case.

W6.6gi opens that effect frontier without reintroducing certificates.
`ReuseCapacityEffectCodeEvaluates` extends the source-only facts-indexed
relation with successful no-result effect nodes that retain the fact map and
consume no allocation budget. Its structural theorem accepts one uniform
direct law and one uniform effect law for every fact map, recovers the
production effect prefix/continuation, and proves the same generated-export
postcondition. `correctReuseBudgetedDirectPersistentCode` instantiates it for
compiler-erased persistent `inc`/`dec`, whose source and target transitions
are both identities. Ordinary ownership updates are the next effect instances;
they must establish nontrivial source ordinary-persistence in addition to
their existing witness/header transport.

W6.6gj adds the first non-identity effect instance. The source theorem
`incValue_ordinaryPersistenceTransport` proves that successful ordinary
reference-count increment neither allocates nor changes a cell's persistence
bit. `effectRuntimeRefines_ordinaryIncrement_reuseCapacity` combines that
fact with the existing compiler inversion, executable increment simulation,
and mapped-header capacity transport. Consequently,
`correctReuseBudgetedDirectPersistentIncrementCode` covers arbitrary finite
interleavings of the complete direct/reuse fragment, compiler-erased
persistent ownership effects, and successful ordinary increments. Recursive
decrement is next; unlike increment, it may release an owned graph and needs a
whole-transition ordinary-persistence theorem.

W6.6gk discharges that recursive obligation. Generic list/array fold transport
and the fuel-indexed `decLocationFuel_ordinaryPersistenceTransport` prove that
successful recursive release changes reference counts and liveness without
changing any cell's persistence bit. `ConcreteReuseCapacityOwnershipFrame`
adds exactly the closure-descriptor agreement consumed by decrement, while a
generic direct-law lift preserves it from the already exposed host/witness
table equations. The effect structural theorem is now parameterized by any
facts-indexed frame with a `ReuseCapacityStateRelated` projection, avoiding a
second structural proof. The endpoint
`correctReuseBudgetedDirectOwnershipThroughDecrementCode` therefore covers
the complete direct/reuse family plus persistent ownership, ordinary
increment, and recursive decrement. Explicit deletion is the remaining
ownership operation.

W6.6gl completes that ownership family. The source theorem
`deleteValue_ordinaryPersistenceTransport` handles both the erased reset
sentinel identity and the ordinary one-cell liveness/reference-count update.
`effectRuntimeRefines_ordinaryDelete_reuseCapacityOwnership` combines it with
the existing production delete call and mapped-capacity theorem.
`effectRuntimeRefines_reuseOwnership` then assembles the exact existing
`OwnershipEffectSupported` union, and
`correctReuseBudgetedDirectOwnershipCode` proves finite whole-export partial
correctness for arbitrary interleavings of every direct/reuse operation with
all persistent and ordinary ownership effects. Constructor/tag and field
mutation are the next effect families.

W6.6gm adds constructor-tag mutation to that facts-indexed endpoint.
`modifyConstructor_ordinaryPersistenceTransport` is the common source
boundary for successful constructor-payload rewrites: the decoded live cell
is replaced while its ownership metadata, including persistence, is retained.
`ConcreteReuseCapacityOwnershipFrame.ofReplaceHeapEffectStep` packages the
matching target-side invariant reconstruction from an executable effect step,
mapped-header capacity transport, source ordinary-persistence transport, and
unchanged frontier. The tag instance combines these generic boundaries with
the existing production compiler inversion and concrete header writer.
`correctReuseBudgetedDirectOwnershipAndTagCode` now proves finite whole-export
partial correctness for arbitrary interleavings of every direct/reuse
operation, the complete ownership family, and successful tag mutation.
Object-field mutation is next and can reuse the same two generic transport
boundaries.

W6.6gn applies those boundaries to both object-field argument forms. The FVar
instance reconstructs the object and field locals, selected descriptor kind,
binary host call, and exact checked write; the erased instance reconstructs
the compiler's canonical zero payload and erased descriptor slot. Both source
steps are instances of `modifyConstructor_ordinaryPersistenceTransport`, and
both target steps cross
`ConcreteReuseCapacityOwnershipFrame.ofReplaceHeapEffectStep`.
`correctReuseBudgetedDirectOwnershipTagAndObjectCode` therefore covers
arbitrary finite interleavings of the complete direct/reuse family with
ownership, tag mutation, and FVar or erased object-slot writes. `USize` and
packed-scalar mutation are the next facts-indexed effects.

W6.6go adds successful `USize` slot mutation. The typed source specialization
`setUSizeSlot_ordinaryPersistenceTransport` reduces the absolute final-LCNF
slot write to the generic constructor-payload transport. The operation law
then reuses the existing compiler inversion, i32/i64 local resolution,
installed concrete setter, mapped-header capacity theorem, and unchanged
frontier. `correctReuseBudgetedDirectOwnershipTagAndFieldMutationCode` covers
the complete direct/reuse and ownership/tag fragment plus both object-field
forms and `USize` fields. Packed-scalar mutation is the remaining current
constructor-field family.

W6.6gp completes that current constructor-field family.
`setScalarField_ordinaryPersistenceTransport` specializes the common
constructor-payload theorem to typed scalar writes. The facts-indexed
operation law retains the existing descriptor-derived packed-coordinate and
non-overlap proof, selects the installed `UInt8`/`UInt16`/`UInt32`/`UInt64`
setter internally, and crosses the common effect-frame transport.
`correctReuseBudgetedDirectOwnershipTagAndAllFieldMutationCode` now proves
finite whole-export partial correctness for arbitrary interleavings of every
facts-indexed direct/reuse operation with the complete current ownership, tag,
object, `USize`, and packed-integer mutation families. Float setters remain
outside the concrete runtime fragment.

W6.6gq opens the facts-indexed control-flow frontier.
`ReuseCapacityBudgetedCodeEvaluates` adds selected case nodes to the same
source-only finite evaluation relation: entering the selected branch retains
the authoritative fact map, source runtime/environment, and remaining byte
budget. The generic
`codeWP_of_reuseCapacityBudgetedCodeEvaluates_exactReturn` consumes the
existing `CaseRuntimeRefines` implementation law and reconstructs the target
case chain from the production compiler. Its first instance,
`correctReuseBudgetedDirectOwnershipTagAllFieldMutationDefaultCases`, proves
the strongest current facts-indexed direct/effect endpoint under arbitrary
nesting of default-only cases.

W6.6gr instantiates the same theorem for both discriminating case families.
`correctReuseBudgetedDirectOwnershipTagAllFieldMutationObjectConstructorCases`
uses the recursive concrete `getTag` chain law for normalized object
alternatives, with or without a trailing default.
`correctReuseBudgetedDirectOwnershipTagAllFieldMutationScalarUInt8Cases` uses
the import-free scalar comparison-chain law. Both endpoints retain the exact
fact map and byte budget across every selected case branch while allowing the
full current direct/reuse and ownership/tag/field-mutation families within the
selected continuation.

W6.6gs generalizes that relation and theorem across response-producing
external `let` nodes. `ReuseCapacityExternalLetRuntimeRefinesWithCost` is the
exact implementation condition: from a source response and path cost it must
execute the production external prefix, prove the validator-selected successor
fact map, and re-establish the indexed frame after binding the response.
External-free case clients use the vacuous instance. Concrete pure
integer/natural/scalar external instances are supplied by W6.6gt.

W6.6gt exposes the reusable transport boundary that those concrete pure
responses already construct. `ExternalLetRuntimeRefinesWithCostAndTransports`
adds the checked destination-local update, witness transport, old-header
capacity transport, and source ordinary-persistence transport to the existing
operation-family law. The ordinary external theorem is now a projection of
this stronger result; no per-program certificate or target artifact enters the
premises. Heap `Int`, representation-polymorphic `Nat`, and nonallocating
scalar results instantiate the boundary using their canonical allocation and
response theorems.

`ConcreteReuseCapacityPureExternalFrame` threads the authoritative reuse fact
map, ordinary-token relation, byte budget, and all three installed handler
laws. The mixed pure-external transport theorem lifts that frame across each
response, applies the validator's ordinary destination-fact erasure, and
retains every unrelated ordinary token.
`correctReuseBudgetedDirectPureExternalDefaultCases` is the first whole-export
endpoint: arbitrary finite interleavings of the complete direct/reuse family,
all proved pure external families, and default-only case wrappers execute the
production Wasm with the exact residual budget.

W6.6gu applies the same mixed frame to the two discriminating case families.
`correctReuseBudgetedDirectPureExternalObjectConstructorCases` reconstructs
the normalized recursive `getTag` comparison chain, while
`correctReuseBudgetedDirectPureExternalScalarUInt8Cases` reconstructs the
import-free scalar chain. Either selected branch may contain further
direct/reuse operations and response-producing pure externals; case dispatch
retains the exact fact map and byte budget.

W6.6gv closes the next composition boundary.
`EffectRuntimeRefines` now exposes exact preservation of the installed
external-handler table, which every proved no-result helper already provides.
Its generic handler-invariant and invariant-transport combinators avoid
re-proving the three pure result laws for each ownership or mutation
operation. `ConcreteReuseCapacityPureExternalOwnershipFrame` is the canonical
combined resource: authoritative facts, ordinary tokens, local alignment,
wasm32 budget, all pure `Int`/`Nat`/scalar handler laws, and host/witness
closure-descriptor agreement.

The direct and external-result families preserve that frame independently,
and the complete ownership/tag/object/`USize`/packed-integer effect union now
does as well.
`correctReuseBudgetedDirectPureExternalOwnershipTagAllFieldMutationDefaultCases`
and its object-constructor and scalar-`UInt8` variants are the first
facts-indexed whole-export theorems to admit all four current structural node
families simultaneously. Their only execution premise is the finite
source-facing evaluation; no target program, branch witness, or execution
certificate appears in it.

W6.6gw opens the interprocedural structural boundary.
`ReuseCapacityBudgetedCodeEvaluates.callLet` adds successful source calls with
only source admission, the finite source call step, response cost, and the
validator-selected fact transfer. `ReuseCapacityCallLetRuntimeRefinesWithCost`
states the exact reusable compiler theorem condition: recover the production
direct-call or closure-dispatch prefix, execute it, preserve installed handler
and descriptor tables, and re-establish the authoritative frame at the
residual byte budget.

The generic code-WP and whole-export theorems now consume this law directly;
existing call-free clients use its vacuous instance. The next slice will
derive a nonvacuous direct-declaration instance from a budgeted hereditary
callee theorem. That callee theorem, rather than any caller-supplied target
certificate, must provide ordinary-token persistence, witness/header
transport, immutable-table preservation, and exact residual allocation
headroom.

W6.6gx defines and connects that direct-declaration boundary.
`BudgetedCapacityPreservingSuccessfulDeclaration` strengthens the existing
hereditary callee result with precisely those four missing transports.
`ConcreteReuseCapacityPureExternalOwnershipFrame.ofDirectDeclarationCall`
combines it with the compiler-derived argument assembly and checked caller
result write, erases only the destination fact, and reconstructs the complete
mixed frame.

`DirectDeclarationCallImplementation` is the remaining recursive program
theorem condition: from source call admission plus actual compiler/adapter
outputs and the caller state relation, derive the generated direct-call prefix
and a budgeted hereditary callee result.
`DirectDeclarationCallImplementation.runtimeRefines` proves that this one
uniform theorem discharges the generic call law. The next work is therefore
not another caller-side adapter; it is to prove this implementation condition
from the generated program's declaration environment.

W6.6gy adds lazy caches to the same certificate-free induction.
`ReuseCapacityBudgetedCodeEvaluates.lazyLet` records only the source cache
path, finite source step, path cost, and validator transfer.
`ReuseCapacityLazyLetRuntimeRefinesWithCost` requires a uniform implementation
theorem to recover and execute the production globals/conditional prefix and
restore the exact residual frame.

`BudgetedCapacityPreservingLazyStep` is the proof-side hit/miss boundary:
existing executable lazy-cache theorems are paired with the checked result
write, ordinary/witness/header transports, immutable-table preservation, and
path-dependent residual budget.
`ConcreteReuseCapacityPureExternalOwnershipFrame.ofLazyCacheResult` performs
the shared fact erasure and frame reconstruction.
The hit constructor proves zero allocation with unchanged store/witness; the
miss constructor accepts the hereditary declaration/publication transports.
Finally, `LazyCacheImplementation.runtimeRefines` reduces the generic
structural law to one generated declaration-environment theorem, parallel to
the direct-call boundary.

W6.6gz closes the executable lazy-miss prefix.
`BudgetedCapacityPreservingLazyStep.miss_of_bodyWP_cacheSet` invokes the
existing compiler-anchored nullary body, concrete `cacheSet`, both Wasm global
publications, and the surrounding miss conditional directly; callers no
longer provide an assembled lazy-step simulation.
`miss_of_budgetedDeclaration_cacheSet` then consumes the same budgeted
hereditary declaration theorem as direct calls and composes its ordinary,
witness, header, immutable-table, and residual-budget transports with the
publication step.

W6.6gza proves the nonallocation property of cache publication from the
executable runtime. `markPersistentFuel_preserves_heapCursor` follows the
recursive constructor/closure graph while composing cursor-preserving header
writes; its public wrapper feeds
`persistGlobalValue_preserves_heapCursor`,
`ConcreteRuntimeState.writeGlobal_preserves_heapCursor`, and finally
`cacheSetStep_preserves_heapCursor`.
`cachePublication_preserves_addressSpaceBudget` turns that exact equality into
the residual resource theorem and `miss_of_budgetedDeclaration_cacheSet` now
derives it internally rather than accepting a publication-budget premise.

The remaining miss proof is now sharply local: show that recursive cache
persistence preserves every unrelated ordinary reuse token and every mapped
allocation extent. The concrete cache execution, callee recursion,
handler/descriptor tables, local write, global publication, heap frontier,
and residual-budget composition are no longer open.

W6.6gzb closes the mapped-allocation half of that local proof.
`LiveHeapRel.writePersistentMetadata` now returns the same-extent header
transport established by its validated header write. The leaf,
constructor/closure child folds, fuel-indexed graph theorem, and public
runtime theorem compose that transport recursively.
`CachePersistenceRefines`, concrete `writeGlobal`, and
`cacheSetStep_of_refines` carry it through the layered runtime, and
`miss_of_budgetedDeclaration_cacheSet` derives publication capacity from the
callee result plus generated cache-slot kind/lookup and descriptor-table
identity. It no longer accepts a free `publicationCapacity` premise.

The last publication-side issue is not an unconditional preservation theorem:
cacheing deliberately marks the returned graph persistent, so a retained
reuse token aliasing that graph ceases to be ordinary. This is a concrete
lazy-cache instance of
`FIR-BUG-wasm-none-reuse-retained-token-ordinary`.

W6.6gzc removes that overstrong premise from the lazy-step interface.
`ReuseTokenOrdinaryBindTransport` is indexed by the authoritative fact map
and preserves ordinaryness exactly for the retained facts that survive
destination erasure. `BudgetedCapacityPreservingLazyStep`, its executable
miss constructors, and the generic lazy-cache implementation now consume that
facts-aware frame. The former all-location
`OrdinaryPersistenceTransport` remains only a sufficient adapter for steps
that genuinely preserve every ordinary cell; it is no longer required of
cache publication. The empty-fact theorem records the conservative alias-safe
endpoint, where publication has no retained ordinary-token obligation.

The remaining validator/integration task is to invalidate facts whose token
locations may be reachable from the published graph, or to provide a proved
reachability-disjointness condition for the facts it retains. W6 can now state
and prove that semantic boundary without weakening the concrete runtime or
assuming an invalid all-location theorem.

W6.6gzd proves the reachability-disjoint branch of that boundary.
`markPersistentLocationFuel_findCell_eq_of_not_reachable` follows the exact
recursive metadata write and owned-field fold and proves that every cell
outside the published root's original `Reachable` closure is unchanged. It
uses the existing ownership-graph frame to transport child reachability
through earlier visits, so cycles and shared subgraphs are covered.
`ReuseTokenPublicationDisjoint` applies this result to precisely the nonzero
tokens selected by the authoritative fact map and environment;
`ReuseTokenOrdinaryRel.markPersistent_of_publicationDisjoint` then preserves
their ordinaryness, and
`ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint` lifts it through the
exact semantic `setGlobal` and result binding. Empty fact maps and non-heap
cache values have constructive adapters.

The executable budgeted miss theorem no longer accepts an opaque publication
frame. It requires the exact source post-state equation
`nextRuntime = callRuntime.setGlobal declaration sourceValue` and the semantic
token/graph disjointness condition, then derives the frame internally. The
remaining generated-environment task is therefore explicit: derive that
post-state equation from the source lazy-miss construction and prove
disjointness for every retained fact, or coordinate a shared validator
transfer that invalidates facts for which disjointness cannot be established.

W6.6gze adds the generated cache-state layer needed to connect a published
miss to a later hit. `PopulatedLazyCacheSlotRel` relates the exact semantic
global entry to its initialized Wasm flag/value pair and the
`PhysicalValueRel` at the declaration's checked result kind.
`PopulatedLazyCacheSlotRel.ofPublication` derives that relation from the
already-executed source `setGlobal` plus the two Wasm `global.set`s.
`BudgetedCapacityPreservingLazyStep.hit` now derives its post-binding
`StateRelated` fact from the cached physical lane instead of accepting it as
an opaque premise; `hit_of_populatedSlot` additionally constructs the checked
destination write from `ConcreteLocalFrameAligned`.
`hit_of_compiledCache` anchors the result to the production
`compileLetValue`/Talos-adapter equations and exact `2 * cacheIndex` layout.

The uniform `LazyCacheImplementation` boundary consequently consumes the
canonical `ConcreteReuseCapacityFrame`, not merely its semantic-state
component: local-frame capacity is a real generated execution resource.

W6.6gzf lifts that state to the complete generated cache table.
`LazyCacheTableLayout` records the checked flag/value pair and singleton
result kind for every initializer. `LazyCacheGlobalsRel` requires every
semantic cache entry to have a generated slot and classifies each slot as
either empty on both sides or populated by a `PopulatedLazyCacheSlotRel`.
`adaptedInitial` establishes the empty relation for the production adapter and
Talos initial store, including resident globals appended after the cache
prefix. `transport` preserves the table through operations that preserve
semantic and physical globals while permitting representation-witness
changes. A semantic lookup forces the corresponding slot to be populated, so
`hit_of_compiledCacheTable` now derives the physical cache lane and complete
generated hit directly from the table invariant.

W6.6gzj removes that remaining semantic-lookup premise from the hit boundary.
`SourceLazyLetResult.hit_cacheFacts` inverts the complete three-step source
execution and proves both that the source runtime is unchanged and that the
named global already contains the returned value. The impossible miss branch
is discharged structurally: one internal-code step cannot remove both the
callee cache frame and the caller binding frame, and one yielded external step
can remove at most the cache frame. `hit_of_compiledCacheTable` now consumes
only source/compiler facts, the source execution, and the canonical cache
table. The contract harness preserves this certificate-free source boundary.

W6.6gzg closes the pointwise publication update.
`LazyCacheGlobalsRel.emptySlot` turns semantic cache absence into the exact
zero physical flag; the value write preserves that flag.
`LazyCacheGlobalsRel.publish` then combines the source `setGlobal` with the
two physical writes, replaces the selected slot by
`PopulatedLazyCacheSlotRel`, and preserves every other slot. Initializer
uniqueness proves distinct source names, while the even/odd pair layout proves
the four required physical-index inequalities. The theorem also preserves
`semanticCovered`, so publication cannot introduce an ungenerated semantic
entry. `withPublishedCacheTable` packages this update with the existing exact
budgeted generated miss at one shared post-state, witness, and final store.

W6.6gzh carries the table in the canonical program invariant.
`ConcreteReuseCapacityCacheFrame` augments the existing reuse-capacity,
pure-external, and ownership frame with `LazyCacheGlobalsRel`.
`adaptedInitial` builds that frame over the production adapter/Talos entry
store. `ofLazyCacheResult` reconstructs the exact successor frame from a
budgeted lazy step plus one path-specific cache transition; it does not
introduce an execution certificate or existential target state. The uniform
`LazyCacheImplementation` law is correspondingly strengthened: an
implementation now consumes the augmented frame and produces the successor
cache table, and `runtimeRefines` targets the same augmented invariant.
Declaration bodies that populate nested cache slots can therefore return
their evolved table instead of being forced through an unchanged-globals
premise.

`listAllUnique_eq_true_iff_nodup` also connects the validator's executable
initializer-uniqueness check to the exact separation fact used by publication.

W6.6gzi reduces and internalizes the validator boundary.
`LazyCacheInitializerSignatures` is the direct source-facing consequence of
the validator's singleton-result loop.
`LazyCacheTableLayout.ofSignatures` proves, by induction over the executable
`cacheGlobalKinds` fold, that those signatures generate the exact flag/value
lanes at `2 * index` and `2 * index + 1`; physical layout is no longer a fact
that integration must restate. `LazyCacheValidationFacts` pairs the remaining
singleton-signature fact with checked Boolean uniqueness.
`LazyCacheGlobalsRel` now carries that bundle, so initial-state construction
derives layout and every publication reuses the stored uniqueness fact instead
of accepting another caller premise.

The monolithic integration-owned `validateModuleShape` checker does not yet
export a proof accessor constructing `LazyCacheValidationFacts` from
successful module validation. That two-field theorem is now the complete
coordination boundary; no offset arithmetic or dynamic cache invariant needs
to cross it.

W6.6gzk repairs `FIR-BUG-wasm-none-lazy-source-step-count`.
`SourceLazyMissResult` replaces the fixed four-step convention with five
structural pieces: staging, cache-miss declaration entry, arbitrary finite
isolated callee execution, semantic publication, and caller bind.
`ExecSteps.withFrameSuffix` lifts the isolated execution under the cache and
caller-binding frames; therefore the witness cannot consume or reconstruct
protected caller frames.
`SourceLazyLetResult.execSteps` composes either path back into the ordinary
finite interpreter relation used by whole-program correctness.
`SourceLazyLetResult.miss_cacheFacts_of_valueEq` then derives initial semantic
absence and the exact `RuntimeState.setGlobal` publication equation directly
from execution. The exact generated miss constructors combine that absence
with `LazyCacheGlobalsRel.emptySlot`, so the zero physical flag is no longer a
caller premise. `cachedHeapFourStepsRemainInCallee` retains the counterexample
to the old contract, while `cachedHeapSevenStepsPublishAndResume` confirms the
nontrivial internal body now publishes and resumes through the structured
protocol.

W6.6gzl closes callee-result alignment without strengthening observations or
assuming unchanged globals. `SourceCodeResult` records the complete terminal
source runtime carried by a yielded state; `SuccessfulDeclaration` retains
that exact result and derives its former observation-facing `ExecEvaluates`
field as an accessor. `ConcreteCodeSimulation.sourceResult` constructs the
exact relation through direct values, calls, externals, lazy caches, cases,
and effects. The general `ExecSteps.final_eq_of_done` theorem identifies the
terminal state of two deterministic finite runs even when `Observation`
deliberately omits globals and the next-location frontier.

`SourceLazyLetResult.miss_cacheFacts_of_callee` applies that theorem to the
isolated miss body and the hereditary declaration result. Static source
lookup, nullary-parameter, and code-body equations identify their common
start; the theorem then derives both initial cache absence and the exact
pre-publication runtime. Consequently
`miss_of_budgetedDeclaration_cacheSet` no longer accepts
`publicationRuntimeEq`. Nested declarations may evolve unrelated cache slots,
and the final semantic publication is derived from execution.

The next cache work is to derive the new static declaration equations and
retained-token publication disjointness from the generated declaration
environment (or coordinate alias-invalidating validator transfer), then use
the same alignment result to construct the successor whole-cache table in the
uniform implementation.

W6.6gzm makes that successor-table construction stable under nested cache
execution. An empty `LazyCacheSlotRel` now retains physical presence of its
unconstrained value lane in addition to the zero flag; validation-derived
layout and the production initial store establish both lanes, and pointwise
transport preserves them. `LazyCacheGlobalsRel.slotLanesPresent` consequently
provides the exact in-bounds facts needed by generated `global.set`
instructions without treating the unpublished zero value as semantic data.

`LazyCacheGlobalsRel.publish` no longer requires the selected slot to remain
semantically empty at the callee's final runtime. It replaces either an empty
slot or a slot populated by nested execution while preserving every distinct
slot through initializer uniqueness and paired-index separation.
`cacheSetStep_preserves_wasmGlobals` and
`LazyCacheGlobalsRel.afterCacheSet` transport the evolved table across the
host-owned persistence update.
`withCacheSetPublishedTable` then composes the host write and the two generated
physical writes into the exact successor table. The remaining uniform
implementation obligations are static generated-declaration selection,
callee-table production, and retained-token publication disjointness (or a
shared validator transfer that invalidates unsafe facts).

W6.6gzn closes the proof-side static cache-selection boundary.
`LazyCacheGeneratedEnvironment` retains the ordered lowering/module cache-name
alignment, validator-derived singleton/uniqueness facts, and exact generated
operation/declaration result-kind agreement once for the complete declaration
environment. Its `select` theorem turns the production `findIdx?` result into
the emitted initializer lookup and exact signature kind. Generated hit and
hereditary-miss theorems no longer accept those two facts independently, and
the uniform `LazyCacheImplementation` structure carries the static environment
alongside its dynamic step implementation.

The attempted compiler derivation exposed
`FIR-BUG-wasm-none-lazy-cache-result-refinement`: source admission allows an
`.object` nullary declaration result to refine a `.tobject` call site, but
lazy lowering types the physical cache lane from the declaration while typing
`cacheSet` and both value-global instructions from the caller. The W6 contract
guard proves that `lowerSupported` accepts this program and production
adaptation rejects its generated module at the value global. W6 therefore
keeps exact result-kind alignment explicit instead of weakening concrete lane
decoding or claiming it follows from the current supported-source predicate.
The shared lowering fix should cache at the declaration's actual result kind
and expose its refinement into the caller destination. After that lands, an
integration-owned accessor from successful `validateModule` to
`LazyCacheValidationFacts`, plus canonical context/module cache-name equality,
can construct the complete generated environment.

W6.6gzo derives the production pipeline portion of that environment.
`lower_of_lowerSupported` exposes the underlying successful `lower` equation,
and `initializers_of_lower` proves directly from the executable lowering that
the emitted module uses exactly `cachedDeclarationNames program`; callers no
longer restate module-side cache-name alignment. `validated_of_adapt` similarly
recovers successful symbolic validation from production adaptation.

`LazyCacheValidatorSound` names the remaining integration-owned obligation as
one theorem quantified over every successfully validated module. It is not a
per-program certificate or a second checker. The attempted local proof
confirmed that unfolding the monolithic `validateModuleShape` duplicates a
large path tree, so the authoritative validator should expose its initializer
uniqueness and singleton-signature loop through a small accessor (or first
factor that loop into a named helper).
`LazyCacheGeneratedEnvironment.ofSupportedPipeline` now combines that one
uniform theorem with actual supported lowering/adaptation, canonical
context-side cache names, and `LazyCacheResultKindsAligned`. Thus the remaining
static conditions are exact and independently owned: integration exposes the
validator theorem, the correctness framework supplies a context constructed
with the compiler's cache-name table, and the shared lowering fix discharges
result-kind alignment. No proof-side cache enumeration or caller-supplied
initializer equation remains.
`ofCanonicalSupportedPipeline` specializes this result to the exact context
shape threaded by lowering, making context-side cache-name alignment
definitional as well.

W6.6gzp closes the hereditary whole-cache miss composition.
`BudgetedCapacityPreservingSuccessfulDeclarationWithCache` is the recursive
declaration theorem for code that may evaluate lazy globals: it pairs the
existing budgeted declaration refinement with the exact
`LazyCacheGlobalsRel` at the callee's semantic runtime, representation
witness, and concrete post-store. This is an induction hypothesis over the
generated declaration environment, not a per-execution target certificate.

`StateRelated.bindAfterCacheSet` derives the caller's complete post-binding
state relation from the hereditary callee relation, concrete `cacheSet`,
compiler-derived result local/kind facts, and the checked local write. The
lazy-miss theorem therefore no longer accepts an opaque `nextRelated`
premise. Its fundamental ownership premise is now only
`ReuseTokenOrdinaryBindTransport` across semantic publication; proved
reachability disjointness remains one sufficient adapter, while a future
alias-invalidating fact transfer may implement the same boundary directly.

Finally, `miss_of_cachedDeclaration_cacheSet` composes the recursive callee,
concrete cache publication, generated value/flag writes, resource transports,
and evolved table into one result containing both the exact budgeted miss and
the successor whole-cache invariant. Nested initializer execution may change
any cache slot; no unchanged-cache premise is used.

W6.6gzq lifts that composition to the canonical program frame.
`miss_of_cachedDeclarationFrame` constructs the executable `cacheSet` result
from the hereditary callee's concrete runtime/value refinement, recovers both
generated physical lanes from its evolved whole-cache table, performs the
checked caller-local write from frame alignment, and derives the immutable
external/descriptor equations definitionally through the host and Wasm global
writes. The declaration-environment induction therefore no longer supplies
`afterCache`, `valueStore`, `nextLocals`, old lane values, the concrete host
operation, or publication table equalities.

W6.6gzr closes that concrete host-slot boundary.
`ConcreteGlobals.staticLayout` exposes the ordered `(name, AbiKind)` table
independently of optional cached values. `staticLayout_declare` proves the
production declaration constructor exact, while `staticLayout_write` and
`ConcreteRuntimeState.writeGlobal_preserves_staticLayout` show that successful
publication changes only the selected optional value even when recursive
persistence updates heap metadata.

`cacheSetStep_preserves_hostStaticLayout` lifts the frame through the
executable Talos host call. `LazyCacheGlobalsRel.hostLayout` retains the exact
`cacheDeclarations source` equation from `adaptedInitial`, ordinary transport,
host publication, and the generated Wasm-global suffix.
Validator-derived singleton signatures prove that `cacheDeclarations` keeps
every initializer name in order; initializer uniqueness therefore makes its
name projection duplicate-free. `LazyCacheGlobalsRel.hostSlot` uses those
facts to derive the selected concrete slot and its exact signature kind.
`miss_of_cachedDeclarationFrame` consequently no longer accepts
`cacheFound` or `cacheKindEq`.

W6.6gzs closes the compiler-derived structural hit branch.
`compileCachedLetValue_inv` inverts a successful production
`compileLetValue` result for a source nullary call, recovering the actual
cache index and exact symbolic flag/branch/value sequence.
`adaptCachedLetValue_inv` then inverts successful Talos adaptation, recovering
both call indices and the exact executable block.
`compileCachedLetValue_adapted_inv` composes these facts directly from the two
pipeline success equations; neither indices nor target code are source
evaluation certificates.

`SourceLazyLetResult.hit_cacheFacts` now ignores arbitrary binder metadata,
and its generic `hit_cacheFacts_of_valueEq` adapter derives both the unchanged
source runtime and populated semantic cache lookup from an actual three-step
source hit. Finally,
`BudgetedCapacityPreservingLazyStep.hit_of_compiler` combines compiler
inversion, local-layout alignment, the generated cache table, and the
canonical runtime frame. It returns the exact zero-cost target hit, checked
caller-local update, authoritative reuse-fact transfer, and unchanged
whole-cache relation from source/static facts plus the real compiler and
adapter outputs. No target execution witness is a premise.

The remaining uniform implementation work is now declaration-environment
induction on the miss branch rather than another caller-side hit/cache lemma.
That branch must select the generated callee/import operations, obtain the
cache-aware hereditary declaration result, and establish the facts-aware
publication transport. Independently, integration still owes the universal
validator accessor, and the shared lowering bug
`FIR-BUG-wasm-none-lazy-cache-result-refinement` still prevents deriving
result-kind alignment for every source program currently admitted by
`lowerSupported`.

W6.6gzt closes the compiler-derived internal miss composition.
`LazyCacheCallSupported` is the common source/static admission relation for
hits and misses: it records only a source nullary call, declaration/result ABI,
and compiled destination local. `LazyCacheInternalMissSupported` adds only the
selected internal declaration body. Neither relation contains cache indices,
numeric calls, target code, physical values, or target executions.

`ConcreteSupportedExport.cacheSetCall` specializes production
resolver/adaptor alignment to the exact value-preserving cache-publication
contract, parameter count, and result count selected by the compiler-derived
runtime call. Successful host resolution also rules out the unrepresented
floating-point kinds, so no separate cache-operation support certificate is
needed.

`LazyCacheInternalMissInduction` states the exact recursive
declaration-environment result at the declaration index selected by production
adaptation: the hereditary cache-aware callee theorem together with
facts-aware ordinary-token transport across publication.
`BudgetedCapacityPreservingLazyStep.miss_of_supportedExportCompiler` composes
that induction result with compiler/adaptor inversion, supported-export import
and local selection, the canonical cache frame, concrete host publication, and
the successor whole-cache relation. Thus the internal miss call site supplies
no target execution, numeric index, host-contract, physical-value, or local
layout certificate.

W6.6gzu instantiates the uniform internal lazy-runtime law.
`LazyCacheInternalSupported` is the source-only hit/miss family used by the
structural code proof. Its hit constructor fixes allocation cost to zero; its
miss constructor retains only the selected internal declaration body and
recursive cost. Neither constructor contains target code, numeric indices,
physical values, stores, witnesses, or executions.

`LazyCacheInternalCalleeInduction` factors the hereditary target theorem from
the source-runtime postcondition required after the declaration returns.
`LazyCacheInternalPublicationInduction` chooses the exact semantic condition:
every authoritative retained reuse token is outside the ownership closure of
the value about to be published. Its `toMissInduction` theorem constructively
derives the former facts-aware publication transport. The weaker
`LazyCacheInternalHereditaryInduction` is already sufficient for non-heap
results, because `publication_of_nonHeapReference` proves their ownership
closure cannot contain a retained heap token.

`LazyCacheInternalDeclarationInduction` quantifies that result uniformly over
all admitted internal misses and canonical caller frames. This is a recursive
module theorem, not a target execution certificate supplied at one call site.
`LazyCacheImplementation.ofInternalCompiler` combines it with the compiler-
derived hit and miss theorems, and
`ConcreteSupportedExport.internalLazyRuntimeRefines` exposes the resulting
`ReuseCapacityLazyLetRuntimeRefinesWithCost` instance consumed by the existing
structural compiler proof.

The remaining heap-result work is therefore a source alias theorem or a
coordinated validator transfer that invalidates retained facts which can reach
the published graph; it is tracked by
`FIR-BUG-wasm-none-reuse-retained-token-ordinary`. External nullary misses
still require their distinct hereditary external-result branch. The universal
validator accessor and exact lazy result-kind alignment remain the independent
shared-contract obligations described above.

W6.6gzv closes publication reasoning for exact non-object result kinds.
`PhysicalValueRel.isNonHeapReference_of_kind` proves that every ABI result
other than `.object` or representation-polymorphic `.tobject` has no semantic
heap-reference ownership root. This covers exact tagged, erased, reuse-token,
integer-width, and scalar lanes directly from the already-proved physical
result relation.

`LazyCacheInternalHereditaryDeclarationInduction` now isolates the ordinary
recursive generated-declaration theorem before publication reasoning, while
`LazyCacheInternalResultKindsNonHeap` is its source-only fragment policy.
`LazyCacheInternalDeclarationInduction.ofHereditaryNonHeap` derives the
complete publication-aware module theorem from those two premises.
`ConcreteSupportedExport.internalNonHeapLazyRuntimeRefines` consequently
exposes the full compiler-generated cache law without a separate alias premise
for that fragment.

W6.6gzw establishes the entry-relative structural boundary needed to build
that recursive module theorem. `ReuseCapacityBudgetedCodeEvaluates.sourceResult`
retains the exact terminal source runtime for mixed direct, external, call,
lazy, case, and effect executions. `ReuseCapacityCodeEntryTransports` packages
entry-to-current witness, old-header capacity, ordinary-persistence,
external-table, and both descriptor-table facts; `refl` initializes the
invariant and `step` composes one operation theorem.
`ReuseCapacityEntryRelativeFrame` strengthens any existing facts-indexed frame
with this bundle, while
`codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelative` reuses the
certificate-free syntax induction and returns the exact source result, target
`CodeWP`, final base frame, and all six entry-to-exit transports. No target
execution is added to source admission.

W6.6gzx makes that structural boundary parametric in caller-owned
address-space slack. `ReuseCapacityBudgetShiftedFrame` presents any
resource-indexed frame at `remainingBytes + slack`. The direct, external,
call, lazy, and effect runtime-law `shiftBudget` theorems prove that every
operation consumes only its source-selected cost and preserves the same
slack; case selection is cost-neutral and needs no adapter.

`codeWP_of_reuseCapacityBudgetedCodeEvaluates_withSlack` consequently starts
from a frame at `requiredBytes + slack` and returns the final frame at exactly
`slack`.
`codeWP_of_reuseCapacityBudgetedCodeEvaluates_entryRelativeWithSlack` combines
that result with the fixed-entry transport invariant, returning the exact
source result, target `CodeWP`, residual caller frame, and all six
entry-to-exit transports. Each slack instantiation may initially name a
different existential target endpoint, so this result alone does not establish
the fixed-post-state residual field required by
`BudgetedCapacityPreservingSuccessfulDeclaration`. Exact-return determinism
must additionally identify those endpoints; no execution certificate is
required.

The remaining construction work is explicit. Each admitted operation family
must rebuild the entry-relative cache frame from its existing
current-to-successor transport package. Production lowering/adaptation must
then select each internal initializer body uniformly, and the resulting
structural proof must supply the cache-aware hereditary declaration package.
W6.6gzx supplies the slack-parametric resource evidence; W6.6hg below packages
it at one fixed deterministic endpoint. The remaining items are module-level
compiler/runtime obligations, not call-site execution certificates.

W6.6gzy closes the first entry-relative cache operation family. The
transport-strengthened pure-external boundary now retains three facts that
its concrete `Nat`, `Int`, and scalar implementations already satisfy:
semantic globals are unchanged, physical Wasm globals are unchanged, and the
concrete host cache layout is unchanged. These are representation-state
facts, not target executions or certificates.

`ExternalLetRuntimeRefinesWithCostAndTransports.reuseCapacityEntryRelativeCache`
uses them to transport the complete `LazyCacheGlobalsRel`, reconstruct the
reuse-capacity/pure-external/ownership frame, and compose the six
`ReuseCapacityCodeEntryTransports` fields. The production theorem
`reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache`
therefore supplies the exact external-family premise required by the
entry-relative structural theorem for a cached internal body. Its contract
guard fixes that public surface.

The remaining operation-family lift is now direct, interprocedural call,
lazy-cache, and no-result effect. Calls and lazy misses must return the
evolved cache table from their hereditary callee result rather than claim
that cache globals are unchanged. Production internal-function selection and
the source-structural completeness step still follow those family lifts
before `LazyCacheInternalHereditaryDeclarationInduction` can be constructed.

W6.6gzz closes the complete current direct-operation family over that
entry-relative cache frame. `DirectLetStepTransports` is the common
current-to-successor package: witness extension, retained-header capacity,
ordinary-source persistence, semantic-global preservation, physical-Wasm-
global preservation, and concrete host-layout preservation. The facts-indexed
direct law now returns this package as an execution property. Local aliases,
immediates, projections, unboxing, and sharing use reflexive/reader
transports; boxing, `Nat`/String literals, constructors, and reuse use their
allocation or rewrite transports. The constructor helper now exposes its
previously implicit Wasm-global and host-layout equalities.

`ReuseCapacityDirectLetRuntimeRefinesWithCost.reuseCapacityEntryRelativeCache`
uses the package to preserve `LazyCacheGlobalsRel`, rebuild the complete
reuse-capacity/pure-external/ownership frame, and extend the six accumulated
entry transports.
`reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache`
instantiates that adapter with the production compiler/runtime theorem; its
contract guard fixes the target-certificate-free surface.

The remaining operation-family lifts are interprocedural call, lazy-cache,
and no-result effect. Call and lazy execution must consume their hereditary
callee's evolved cache table, while cache-neutral effects can use an explicit
unchanged-global transport package. Production internal-function selection
and source-structural completeness still follow those lifts.

W6.6h closes the complete current no-result effect family over the
entry-relative cache frame. `RuntimeStepTransports` is now the common
cache-neutral representation package shared by direct and effect operations.
`EffectStepTransports` inherits its exact immutable-table preservation, and
`EffectRuntimeRefinesWithTransports` retains that package through
source-family union, handler-table invariants, and equivalent frame
presentations.

Every production effect leaf constructs the strengthened result:
compiler-erased persistent operations use reflexive transports; increment,
recursive decrement, deletion, tag mutation, object-field mutation, `USize`
mutation, and every supported packed-scalar mutation use their exact
same-witness heap transports. `RuntimeAuxEq` supplies the semantic-global
fact uniformly, including new reusable deletion and constructor-mutation
corollaries. Physical Wasm globals, the concrete host cache layout, and both
descriptor tables are definitionally unchanged by the concrete heap
replacement.

`EffectRuntimeRefinesWithTransports.reuseCapacityEntryRelativeCache`
transports `LazyCacheGlobalsRel`, preserves the unchanged validator fact map,
rebuilds the canonical pure-external ownership frame, and extends all six
entry transports. The production theorem
`effectRuntimeRefines_reuseOwnershipTagAndAllFieldMutation_pureExternal_entryRelativeCache`
and its contract guard close the complete current effect premise without
adding target evidence to source admission.

The remaining operation-family lifts are interprocedural call and lazy-cache.
Both must consume the evolved cache relation returned by hereditary execution;
they cannot use the cache-neutral unchanged-global adapter. Production
internal-function selection and source-structural completeness still follow
those lifts before the generated declaration induction can be constructed.

W6.6ha closes the evolved-cache entry adapters for direct declaration calls
and the current non-heap internal lazy family. The endpoint-exact
`ofDirectDeclarationCallExact` theorem now reconstructs the caller frame at
the hereditary callee's actual post-store and witness instead of hiding them
behind existential successors.
`DirectDeclarationCallImplementationWithCache` strengthens the generated
direct-call selection condition with the callee's evolved
`LazyCacheGlobalsRel`, and `runtimeRefinesEntryRelative` threads that table
while composing the callee's witness, capacity, ordinaryness, and immutable
table transports from the fixed declaration entry.

Lazy hits are semantic runtime identities. For misses,
`miss_ordinaryTransport_of_internalCompiler_nonHeap` combines the hereditary
callee's entry-to-return ordinaryness with the fact that publishing a
non-heap result leaves the semantic heap unchanged.
`LazyCacheImplementationWithEntryTransports` packages this path-sensitive
fact alongside the existing compiler-derived hit/miss implementation.
Its entry-relative runtime theorem uses the exact evolved table returned by
the implementation, never an unchanged-global premise. The production
`internalNonHeapLazyRuntimeRefines_entryRelativeCache` theorem and contract
guard close the current lazy premise.

W6.6hb moves production call selection onto that evolved-cache boundary.
`DirectInternalCallSite` and `SaturatedClosureCallSite` retain only source
lookup/evaluation facts and the actual compiler equations; neither contains a
numeric target, concrete address, physical result, target body, or target
execution. `DirectDeclarationCallImplementationWithCache.ofInternalCompiler`
inverts the generated argument-plus-declaration call, derives physical
arguments from `compileArgs`, obtains both local indices from
`LocalLayoutAligned`, constructs the checked destination write from the
canonical cache frame, and delegates only the hereditary callee theorem to
`DirectInternalCallDeclarationInduction`.

The closure sibling factors the common resource proof through
`ofBudgetedCallStepExact` and
`ConcreteReuseCapacityCacheFrame.ofSaturatedClosureDeclarationExact`.
`SaturatedClosureDispatchSelectionInduction` must return an exact equality
between the production candidate fold and its resolved first-match cases.
`SaturatedClosureCallImplementationWithCache.ofInternalCompiler` feeds that
equality to `instructions_compileClosureDispatch`, so the adapted target
program is derived rather than supplied by the induction. Its entry-relative
runtime theorem threads the selected callee's evolved `LazyCacheGlobalsRel`
just like a named call.

The remaining call work is constructive discharge of
`SaturatedClosureDispatchSelectionInduction` from the concrete closure
representation, resolver contracts, fixed-capture projections, and the
hereditary declaration family. Once that and the corresponding uniform named
declaration induction are built, the call branch can be installed in the
syntax-directed body theorem and construct
`LazyCacheInternalHereditaryDeclarationInduction` recursively for the
generated declaration environment. Underapplication remains the separate
allocating closure branch. Heap-valued cache publication remains a separate
extension because it cannot satisfy the current all-location
`OrdinaryPersistenceTransport`; it will require a deliberately weaker entry
invariant or coordinated alias/fact invalidation, not an unsound
unchanged-heap adapter.

W6.6hc begins the constructive saturated-selection discharge at the concrete
matcher boundary. `PhysicalValueRel.heapAddress` proves that either admitted
object-like ABI lane for a semantic heap reference contains the exact mapped
wasm32 address. `StateRelated.resolveClosureMatcher` combines that fact with
the source local lookup and live semantic closure cell to derive both the
physical local and the exact executable `closureMatchesStep` result. Its only
non-state premises are the two immutable closure-table equations already
required by the concrete matcher.

`ClosureCandidateCase.matched_eq_of_refines` consequently makes every
candidate bit a theorem of the semantic closure identity.
`exists_first_nonzero` supplies the generic finite first-match split, and
`closureCandidates_exists_first_match_of_refines` combines them: once the
production candidate enumeration contains the closure's function, total
arity, and fixed-capture count, the complete nonmatching prefix and selected
nonzero case follow constructively. The contract harness fixes both the local
matcher boundary and the first-match theorem; it does not accept a physical
address or target execution.

This inspection exposed
`FIR-BUG-wasm-none-closure-dispatch-frame-agreement`: the canonical W6
reuse/capacity/cache frame retains host/witness closure-descriptor equality
but loses the corresponding closure-dispatch equality. Initial construction
and the concrete operations preserve both immutable tables, but
`closureMatchesStep_of_refines` cannot be invoked from the current composed
frame until dispatch agreement is threaded through direct, effect, call,
lazy, entry-relative, and hereditary transports. The next closure slice is
that invariant lift, followed by a production candidate-coverage theorem from
`compileClosureCandidatesForTarget` and resolver facts. Matcher outcomes must
not be postulated through `ClosureCandidateCase.operation` as a workaround.

W6.6hd closes that immutable-table invariant gap.
`ClosureTablesAgree` names agreement between the concrete host and
refinement witness for both closure dispatch and closure descriptors, while
`ClosureTablesTransport` packages preservation of both tables on the host and
witness sides across one step. `RuntimeStepTransports`, effect transports,
budgeted hereditary declarations, lazy hit/miss steps, and fixed-entry
transports all carry the common package. Direct operations, pure externals,
effects, named and saturated calls, and cache publication reconstruct the
agreement with one shared composition theorem.

`ConcreteReuseCapacityCacheFrame` now carries that paired agreement beside
`LazyCacheGlobalsRel`. Its canonical matcher accessor derives the exact local
address and executable `closureMatchesStep` without separate table premises,
and its first-match accessor derives the nonmatching-prefix/selected split
from semantic identity coverage. Contract guards exercise both boundaries.
`FIR-BUG-wasm-none-closure-dispatch-frame-agreement` is fixed. The remaining
saturated-selection task is purely static/source-facing: derive semantic
candidate coverage from `compileClosureCandidatesForTarget` and declaration
resolution, then feed it to this canonical accessor. After that, construct
`LazyCacheInternalHereditaryDeclarationInduction` recursively for the
generated declaration environment.

W6.6he closes that static candidate-coverage slice.
`SaturatedClosureCallResolution` separates an exactly saturated source call
from the existing underapplication family: it records the live semantic
closure, resolved declaration and ABI, exact capture-plus-argument arity,
argument refinement, result kind, code body, and source parameter binding.
From those facts, `candidateSource_exists` proves membership in the real
`compileClosureCandidatesForTarget` enumeration, and
`containsCandidateIdentity` transfers that membership to any exact adapted
candidate list at the mapped address. The canonical cache frame recovers that
address before executable candidate construction and then derives the first
match without a target certificate.

`SaturatedClosureCandidateResolutionInduction` is the new production-facing
hereditary boundary: it supplies an implementation only for a compiler
candidate whose source identity is already proved. Its `toSelection` theorem
discharges enumeration, address recovery, and selection, and
`ofInternalCompilerResolved` builds the complete saturated-call law.
`FIR-BUG-wasm-none-saturated-closure-site-shape` is fixed. The next call slice
must construct this induction recursively from the generated declaration
environment (and ultimately derive source resolution from closure-flow
well-formedness); it must not reintroduce target execution evidence.

W6.6hf corrects the constructive order at that boundary.
`ClosureCandidateCase` contains a successful concrete matcher execution, so a
family indexed by every wasm32 word was uninhabited at unmapped or non-closure
addresses. `ConcreteReuseCapacityCacheFrame.resolveClosureAddress` now derives
the unique mapped word from source resolution and the ordinary state relation
first. `SaturatedClosureCandidateResolutionInduction` constructs candidates
only at that address; `toSelection` then derives semantic coverage and the
first executable match. This fixes
`FIR-BUG-wasm-none-saturated-candidate-arbitrary-address` without weakening
decoding or adding a target execution certificate. Recursive hereditary
declaration construction remains the next call slice.

W6.6hg closes the hereditary declaration packaging boundary exposed by the
entry-relative structural theorem.
`CodeWP.exactReturn_unique` proves that two exact-return `CodeWP` executions
from the same target configuration name the same post-store and physical
result. `ConcreteReuseCapacityCacheFrame.withBudget` then re-runs the
slack-parametric structural proof at any caller budget and transports its
residual frame back to the canonical endpoint.

`budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates` packages
one exact source/target execution, all entry transports, universal residual
budget, and the evolved whole-cache relation as
`BudgetedCapacityPreservingSuccessfulDeclarationWithCache`.
`PhysicalValueRel.ofRefines` and the two declaration `ofRefines` adapters
expose that same package at an admitted caller-facing ABI superkind without
changing execution or cache state. This fixes
`FIR-BUG-wasm-none-slack-existential-uniform-budget`. The next slice constructs
the recursive hereditary declaration family from generated declarations and
uses these packages in named and saturated calls.

W6.6hh removes an accidental shared-context premise from that recursive
boundary. `lowerDecl` computes `localKinds` and transient `joins` separately
for every declaration, so a callee package cannot in general be indexed by
the caller's compiler context. `DeclarationContextsCoherent` now records only
the genuinely module-wide fields—the source program and lazy-cache declaration
table—and direct named calls, saturated closure dispatch, and internal lazy
misses existentially return their callee's coherent declaration context.

Exact source execution transports between coherent contexts because canonical
source machine states observe only `context.program`; the callee's target
`CodeWP`, local alignment, and compiler adaptation remain at its own context.
This fixes
`FIR-BUG-wasm-none-recursive-callee-context-aliasing`. The next recursive slice
must build each `ConcreteSupportedDeclaration` and its context from the actual
`lowerDecl`/adapter function row and feed the result into the hereditary
declaration package. It must not recover the old interface by equating
declaration-local kinds or joins.

W6.6hi closes the remaining local-layout premise in that production selector.
`lowerDecl` now constructs one canonical parameter-plus-body-local binding row
and uses it for both symbolic lookup and the emitted function. The adapter's
name-directed numeric lookup therefore traverses exactly the compiler row, and
`LoweredInternalDeclaration.localsAligned` proves the index and ABI-kind
agreement directly. `collectLocals` retains its public result type and behavior
while exposing a proof-transparent `partial_fixpoint` core, so later static
compiler proofs need not duplicate its recursion.

`ConcreteGeneratedDeclaration.exists_ofSupportedPipeline` now derives the
callee context, function row, body adaptation, and local alignment from the
actual `lowerSupported`/`adapt` equations without a caller-supplied layout law
or declaration-hygiene premise. No semantic Wasm ABI or concrete-runtime
contract changes. The next slice assembles these generated declaration rows
into the module-wide hereditary declaration family and then exposes the clean
whole-export partial-correctness theorem.

W6.6hj assembles the static half of that family.
`ConcreteGeneratedDeclarationFamily` universally selects every internal
value-returning declaration from any coherent caller context and returns its
exact declaration-local compiler context plus the matching symbolic/concrete
function row. `ofSupportedPipeline` constructs the entire family once from
the two production `lowerSupported` and `adapt` equations; named calls,
saturated closure dispatch, and lazy misses no longer need separate static
compiler selectors.

The family deliberately contains no dynamic target execution. The remaining
hereditary step is semantic: recurse over admitted finite source executions,
apply the selected row's structural body theorem, and feed the resulting
cache-aware declaration package to named, saturated, and lazy call laws. Once
that recursive knot is closed, the root row can expose the whole-export
partial-correctness theorem without a simulation or translation-certificate
premise. No semantic Wasm ABI or concrete-runtime contract changes.

W6.6hk retains the missing callee-entry component of the production family.
`ConcreteGeneratedInternalDeclaration` extends each selected generated body
with the exact parameter row returned by `addDeclarationParams` and its
identity with the emitted symbolic function parameters. This is necessary to
construct a recursive callee's initial local frame from source arguments and
physical Wasm operands; body-local alignment alone cannot establish that
entry relation. The module-wide family now returns this stronger static row.
`DirectInternalCallSite` retains the matching source-only validator facts:
the declaration's effective parameter/result kinds and the argument/result
refinement equations accepted by production support.

No source or target execution is stored in the row. The next proof derives
argument-to-parameter ABI refinement from production support, constructs the
empty-entry reuse-fact/cache frame for each callee, and then performs the
well-founded semantic induction over finite source executions. No semantic
Wasm ABI or concrete-runtime contract changes.

W6.6hl connects that retained static row to the dynamic argument relation.
`ConstructorArgumentsRelated.ofKindsRefine` lifts an exact physical/source
argument relation across the validator's complete pointwise ABI-refinement
decision, reusing `PhysicalValueRel.ofRefines` and changing neither bits nor
semantic values. The generated declaration selector also inverts the actual
successful `lowerSupported` traversal and retains the shared declaration-
parameter uniqueness fact on the selected row. Thus the duplicate-identifier
case fixed by `WASM-DECLARATION-PARAMETER-UNIQUENESS` is unavailable in the
callee-frame proof itself rather than being assumed by its caller.

This remains compiler verification: both facts are derived from production
validation/lowering equations and contain no target execution. The next slice
proves that the unique `addDeclarationParams` row is exactly the source-order
parameter-kind row, uses it to establish `EnvLocalsRelated` for
`targetFunction.toLocals`, and lifts the caller's heap/cache/runtime fields to
the empty-facts callee-entry frame.

W6.6hm closes the parameter/local part of that callee-entry frame.
`ConcreteGeneratedInternalDeclaration.sourceParameterBindings` proves from
the real `declarationParameterKinds?`, `addDeclarationParams`, and emitted
function equations that front insertion plus emission reversal produces
exactly the source-order `(FVarId, AbiKind)` row. The proof derives `Nodup`
parameter names from the production validator's count decision; it neither
assumes a hygiene certificate nor defines a second lowering relation.

`entryEnvLocalsRelatedOfArguments` then composes that row theorem with the
actual `bindParams` result, the caller's `ConstructorArgumentsRelated` row,
and the validator's ABI-refinement decision. Its conclusion is the exact
`EnvLocalsRelated` required by `StateRelated` for
`targetFunction.toLocals physicalArgs`, matching the double reversal in the
Talos direct-call convention. The next slice reuses the caller's unchanged
store/runtime/witness/cache/closure-table fields, supplies empty reuse facts,
and packages this local theorem as a complete
`ConcreteReuseCapacityCacheFrame` at generated callee entry. That frame is
the final setup lemma before the finite-execution hereditary induction.

W6.6hn packages the complete generated direct-callee entry invariant.
`ConcreteReuseCapacityCacheFrame.generatedDirectCalleeEntry` starts from a
valid caller frame and the production-selected call/declaration rows, then
re-indexes the unchanged concrete store at the callee. The argument theorem
supplies the callee locals; reuse facts and ordinary-token obligations are
empty at function entry; parameter and local frame sizes follow from the
actual emitted signature; runtime, failure, allocation budget, external
implementations, descriptor agreement, lazy caches, and closure tables are
inherited unchanged.

The public contract regression requires only the caller frame plus the
production-admitted direct call. It has no separately supplied translation
certificate or callee invariant. The remaining W6.6 proof is the hereditary
finite-execution induction: use this entry frame at every generated internal
call, apply the already proved expression/runtime cases to each finite source
evaluation constructor, and return the resulting observation refinement.

W6.6ho closes the exact-budget production induction step and fixes
`FIR-BUG-wasm-none-direct-callee-budget-premise`. The enclosing structural
call law already checks `stepCost ≤ remainingBytes`, but the direct-call
implementation and module-induction interfaces previously discarded that
fact before asking the callee theorem for an executable exact-cost package.
Both interfaces now retain it.

`generatedDirectCalleeEntryAtCost` weakens the caller-owned concrete budget to
the finite source body's exact allocation cost, while
`targetParameterCount` proves that the production physical argument row has
the adapted callee arity. The generated-declaration
`budgetedDeclarationWithCache_of_reuseCapacityBudgetedCodeEvaluates` theorem
then combines that entry, one finite source-body evaluation, and the uniform
operation-family laws into the complete cache-aware hereditary declaration
package used by the caller. This is the first executable recursive induction
step: its source evaluation is the partial-correctness premise, and no target
execution or translation certificate is supplied.

The next slice defines the source-only hereditary finite-evaluation relation
whose direct-call constructor contains the callee body and continuation
derivations. Induction over that derivation will instantiate the theorem above
recursively, rather than accepting a module-wide callee theorem as an opaque
premise. Saturated closure dispatch and lazy misses then join the same source
derivation with their existing production selection laws.

W6.6hp introduces that source-recursive boundary.
`ReuseCapacityDirectHereditaryCodeEvaluates` follows the existing facts-indexed
finite source relation, but its direct-call constructor contains both the
finite callee-body derivation (at empty declaration-entry facts) and the finite
caller-continuation derivation. `DirectInternalCallSite.sourceCallLetResult`
reconstructs the executable interpreter call prefix from the call equations:
it stages and enters the declaration, lifts the isolated callee execution
beneath the protected caller binding frame, and resumes the continuation.

The hereditary relation erases to `ReuseCapacityBudgetedCodeEvaluates` and
therefore to the exact terminal `SourceCodeResult`. Its call-support payload
contains the nested source derivation needed by recursive compiler
correctness, but no target program, store, witness, execution, or translation
certificate. Compiler contexts are retained only to select each declaration's
real local/static compilation environment; coherent contexts have the same
source program, so this does not alter source execution.

The next slice makes the production direct-call runtime law consume this
hereditary support payload. The declaration-family selector supplies the
generated callee row and the induction hypothesis supplies its exact
cache-aware execution package. That removes the current opaque
`DirectInternalCallDeclarationInduction` premise for direct named calls.
Saturated closure dispatch and lazy misses remain subsequent constructors.

W6.6hq tightens the recursive source boundary before that induction step.
Every hereditary direct-call node now carries the exact
`LoweredInternalDeclaration` produced by the executable source lowerer, and
its nested callee derivation is indexed by that row's canonical context.
Admission predicates are context-indexed, so each recursive body uses its own
direct, external, lazy, case, and effect compiler policy rather than silently
reusing its caller's local context.

`exists_ofSupportedPipelineAtLowered` proves that the exact row carried by the
source derivation occurs in the real `lowerSupported`/`adapt` output. The
remaining numeric call-index identity exposed
`FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness`:
`ConcreteSupportedExport` currently drops the phase boundary's
`Program.NamesUnique` fact, even though import-first named-call resolution can
disagree with source lookup on duplicate internal/external names. The next
isolated contract slice retains that existing source well-formedness fact,
proves exact call-index selection, and then closes the hereditary production
call law by its nested induction hypothesis.

W6.6hr closes the production named-call selection seam. The supported-export
contract retains the phase's `Program.NamesUnique` invariant. Successful real
lowering maps unique source declaration names to a unique symbolic function
table; runtime imports have no declaration key, and a distinct external
declaration cannot shadow the source-selected internal row. Consequently
`ConcreteGeneratedInternalDeclaration.callIndexEq` identifies the adapter's
executable numeric lookup with that exact generated row.

`DirectDeclarationCallImplementationWithCache.ofHereditaryInternalCompiler`
now consumes the hereditary call payload directly. It recovers the production
callee row at the exact `LoweredInternalDeclaration` context, constructs the
callee entry frame from related arguments, invokes correctness of the nested
finite source derivation, and reinterprets its result at the caller ABI. The
call site supplies no target index, target execution, or translation
certificate. `FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness`
is fixed at the compiler-correctness boundary.

The remaining direct-call slice proves
`DirectHereditaryGeneratedDeclarationInduction` itself by structural induction
over `ReuseCapacityDirectHereditaryCodeEvaluates`, using the generated-row
direct/external/case/effect operation families and this new recursive call law.
That theorem, rather than the compatibility
`DirectInternalCallDeclarationInduction`, is the direct named-call component
of the final whole-export partial-correctness result. Saturated closure and
lazy-miss constructors remain subsequent extensions of the same source
derivation.

The current W6 recursive checkpoint closes those subsequent constructors and
the public finite whole-export theorem. The structural relation now admits
arbitrary finite nesting of generated named calls and exactly saturated
closure calls, selects every callee through the real lowering/adaptation row,
and derives the target run by induction on the finite source execution.
`ConcreteSupportedExport.correct_reuseCapacityProductionHereditary` returns
the same semantic value and runtime through the declared result ABI and
accepts no target execution or translation certificate.

Closure candidate packaging is now internal as well. A first version made a
static resolver promise successful matcher execution for every arbitrary
store and address; invalid addresses correctly trap, so that premise was
uninhabitable. The repaired boundary keeps only static compiler, adapter, and
host facts, derives matcher miss/hit behavior at the actual related live
address, and records the discrepancy as
`FIR-BUG-wasm-none-closure-resolver-invalid-address-totality`. The final
packaging step inverts successful adaptation of the actual nested candidate
chain, reconstructs the exact flat-map enumeration and every matcher
import/contract row, and discharges the resolver environment from the public
theorem. The remaining major proof direction is the separately stated
finite-trace/weak-simulation extension for divergence; it does not require a
termination proof for source programs.

The finite-trace extension now has an explicit checked boundary. The generic
`ObservedWeakSimulation` transports exact-length paths between heterogeneous
transition systems while relating the observation at every reached
configuration. `RankedObservedWeakSimulation` additionally requires every
zero-target-step match to decrease a natural-number source rank, so infinite
silent stuttering cannot masquerade as target progress.

`ConcreteRankedTraceSimulation` specializes that interface to deterministic
LCNF `ExecSteps` and the W6 concrete world/event trace relation. Its
`execSteps` theorem already states the desired non-terminating-program-safe
result: every finite source prefix has a finite target prefix with the same
world and exact external-event trace modulo the existing address refinement
witness. This statement contains no target execution certificate and no
termination premise.

The first target implementation boundary is now checked. A
`ResumableWasmState` stores the concrete Talos store, locals, and residual
outer program; `ResumableWasmStep` consumes one instruction only after a
finite `execOne` fallthrough exposes the successor. Fuel monotonicity proves
that every finite path has one common bound and agrees exactly with the
residual `exec` above it. The fallthrough, general return, and compiler-emitted
`.ret` adequacy theorems then recover the exact successful `Wasm.run` result.
`concreteResumableWasmMachine` packages this state and step relation for
`ConcreteRankedTraceSimulation`.

That boundary alone does not solve divergence inside an atomic Talos
`execOne`. The emitted-subset machine below now supplies the reified
call/control stack; the remaining adequacy proof collapses its finite terminal
paths to the checked instruction-boundary/Talos theorem. W6 then constructs
the compiler relation and rank from lowering/adaptation plus the existing
runtime operation laws. The current terminating whole-export theorem becomes
a corollary of that stronger relation; it is not discarded or repackaged as a
certificate.

The adapter inventory and first collapse layer are now checked in
`StructuredWasmFrames`. The relevant emitted structured grammar is direct
calls, zero-arity blocks/loops/conditionals, indexed branches, `.ret`, and
ordinary atomics. Exact frame laws collapse a finite internal call ending at
generated `.ret`, block fallthrough or `br 0`, loop fallthrough, and either
selected conditional body back to their outer Talos instruction step. The
next implementation slice packages these laws into an explicit frame stack
and adds loop restart plus outward branch propagation before the compiler
relation is instantiated.

That explicit stack is now implemented in `StructuredWasmMachine`. Its
control distinguishes running code, branches in flight, returns in flight,
and halted values; its frames cover labels, loops, and direct calls. Ordinary
instructions and imported calls delegate to Talos `execOne`, while internal
calls, structured entry/exit, loop restart, outward branching, return
unwinding, and halting are genuine target steps. The concrete ranked-simulation
alias now selects this structured machine. The next proof folds finite terminal
stack paths through the local collapse laws to the already checked
instruction-boundary `exec`/`run` adequacy result.

### W6.7 completion ladder: compiler-produced finite-trace simulation

The agreed primary theorem direction is a certificate-free ranked forward
simulation. It is not a theorem parameterized by a caller-provided relation:
the supported compiler pipeline must construct the relation and its initial
proof. It preserves every finite source prefix, so it applies equally to
prefixes of terminating and nonterminating executions. Terminating export
correctness becomes a corollary; a backward simulation is deliberately later.

| Stage | State | Acceptance boundary |
|---|---|---|
| W6.7a generic ranked weak simulation | complete | `execSteps` transports any finite source prefix for a constructed simulation, with exact world/trace observations and a strict rank decrease on zero-target-step matches |
| W6.7b instruction-boundary Talos adequacy | complete | finite residual-instruction paths agree with Talos `exec` above one common fuel bound and recover exact `Wasm.run` exits |
| W6.7c emitted structured target | complete | frame laws plus the explicit label/loop/call stack expose progress through calls, branches, loops, returns, and halting |
| W6.7d structured terminal adequacy | complete | every reachable canonical-entry-to-halted path collapses to the exact instruction-boundary/Talos run; stack shape and arities are proved, not assumed at the public boundary |
| W6.7e compiler relation and rank | in progress; direct return, silence, the complete resource-indexed direct-value spine, pure external-result lets, generated lazy-cache hits and non-heap misses, erased default-only cases, arbitrary normalized object-constructor and scalar `UInt8` dispatch, all persistent and ordinary ownership effects through explicit deletion, constructor-tag, both FVar/erased object-field mutation, `USize` and all supported packed-integer field mutations, and arbitrary finite nesting of generated named and exactly saturated closure calls are complete; the terminating fragment now starts at compiler-produced canonical source/target body entries | each admitted LCNF `executeStep` produces a finite structured path restoring compiled code, locals/environment, heap, continuation, trace, closure, ownership, cache, allocation, and ABI invariants; zero-step matches decrease a compiler-derived structural rank |
| W6.7f public finite-trace theorem | pending | `ConcreteSupportedExport` constructs `ConcreteFiniteTraceCorrect` for compiler-produced initial states without a target path, simulation/certificate, resolver package, or termination premise |
| W6.7g corollaries | pending | finite whole-export correctness follows from W6.7d/f; infinite source progress and trace preservation follow from W6.7e/f; backward weak simulation remains explicitly deferred |

W6.7e initially follows the same admitted production fragment as
`correct_reuseCapacityProductionHereditary`: direct operations, supported pure
externals, lazy/cache operations, selected cases, ownership/tag/integer-field
effects, generated named calls, and exactly saturated closure calls at
arbitrary finite nesting depth. Additional LCNF admission and W7 resident
helper refinement are separate widenings, not reasons to weaken this theorem.
W7 may continue in parallel; its helper theorems and the final zero-import
`prettyM` acceptance theorem follow after the core compiler simulation.

The current W6.7e body boundary derives exact Talos execution from existing
runtime WP laws and reifies straight-line generated prefixes as structured
finite paths beneath arbitrary code and frame suffixes. The direct source
`let` constructor restores the recursively compiled focus without accepting a
target execution or translation certificate. The real compiler and adapter
now discharge the target-shape premise for every operation in
`ReuseBudgetedDirectSupported`, including mixed local/erased constructor
arguments and reuse-token prefixes. The resource-indexed recursive induction
composes those direct `let` paths with the final return and retains exact
source/target path lengths. The hereditary structured induction now stages the
real generated named call, enters its exact declaration row, applies itself
recursively to the callee, transports the evolved resource/cache invariant
back to the saved caller, and resumes the compiled continuation. Both machine
paths and the enclosing frame stacks are explicit, while the premises remain
source-only. The same induction now covers every admitted pure `Nat`, `Int`,
and scalar external result. Production compiler/adapter inversion derives the
flat argument/import/result-store prefix, whole-pipeline external alignment
proves that the selected declaration call is a target import, and the existing
entry-relative runtime theorem supplies the evolved heap witness and exact
three-step source request protocol. Generated lazy-cache hits and non-heap
misses are now in that same recursive theorem. Compiler inversion recovers the
flag/value indices and miss body. A populated slot takes the exact five-step
hit path without entering the miss body. An empty slot takes the three-step
initializer-entry prefix, applies the same theorem recursively to the exact
generated declaration row, and then takes the eight-step concrete
cache/publication suffix before resuming the caller continuation. The source
and target paths retain exact step counts, and the complete cache/resource
invariant plus arbitrary saved frame suffixes are reconstructed. Non-heap miss
results make publication disjoint from retained ordinary reuse tokens;
heap-valued misses still require reachability-sensitive fact invalidation. The
first selected case nodes are connected as well. A default-only source case
takes one exact interpreter step while production compilation erases the
wrapper, so the target path is reflexive over the identical recursively
compiled branch and every resource invariant is unchanged. The fragment still
records its empty source join environment explicitly. A singleton object arm
now follows the exact generated `getTag`/tag-comparison/conditional prefix,
recurses under the compiler-created label frame, and takes the corresponding
`returnLabel` step. Two ordered object arms plus a default are connected too:
the proof covers the first hit, the second hit after one miss, and default
selection after two misses, with exact paths and one nested label per executed
test. The same argument is now structural over arbitrary normalized object
tables: compiler inversion peels each generated test, a hit enters its arm, a
miss recurses on the compiled suffix, and the final exact path has five steps
and one label per tested constructor. Arbitrary scalar `UInt8` tables are now
structural too: they use the analogous direct four-step test chain, with no
host import and the same exact label discipline. Persistent `inc` and `dec`
are recursive too: each takes exactly one source step, follows the production
compiler's erased continuation with a reflexive target path, and preserves the
complete entry-relative cache/resource frame before applying the same
induction to the continuation. Successful ordinary increment and recursive
decrement are connected as well: compiler inversion fixes each two-instruction
local-read/imported-call prefix, the concrete operation contract produces the
updated heap, and a shared same-witness transport theorem re-establishes the
full entry-relative frame before continuation recursion. Decrement may release
an ownership tree, so its proof additionally consumes the closure-descriptor
agreement and the recursive ordinary-persistence theorem already carried by
that frame. Explicit deletion is connected through the same generated prefix
and frame reconstruction. Its physical-zero path is available only through the
erased-value relation, while ordinary objects retain mapped live-cell decoding.
Constructor-tag mutation is connected too: its source live-constructor facts
drive the concrete header writer under the compiler-selected `setTag` import,
and the same heap-effect reconstruction restores the recursive frame. FVar
object-field mutation is connected through an exact three-step two-local/call
prefix; descriptor-slot alignment relates the replacement at the selected ABI
kind before the concrete slot writer updates the heap. The erased form is
connected by the analogous three-step object-local/constant-zero/call path;
zero is justified only by the erased ABI relation. `USize` mutation is now
connected by the exact three-step object-local/`i64`-local/call path, using the
checked absolute-slot writer while preserving the witness and heap frontier.
Packed-integer scalar mutation is connected through one common three-step
continuation rule: production state refinement selects i32 for `UInt8`/16/32
and i64 for `UInt64`, while the four checked writers establish their exact
layout-preserving heap updates. The saturated-closure construction has now
crossed its first structured-control boundary too.
`ClosureCandidateCase.matcherFinitePath` derives each concrete matcher call
directly from the resident host contract, and
`structuredWasmResolvedClosureCandidateChainSelectedPrefixFinitePath`
executes the real compiler fold to the first matching candidate. A prefix of
`n` failed candidates followed by the selected one takes exactly
`3 * (n + 1)` target steps and leaves the selected body under the exact `n +
1` nested conditional frames; failed matchers are proved store-neutral, while
the selected matcher's ownership-consuming store is retained. No candidate
execution or branch-selection certificate is supplied. The selected
capture/argument prefix is now exact too.
`ClosureCaptureRows.structuredFlatProgram_of_adapted` proves that erased
captures become constants and represented captures become resolver-proved
imported projections, while the ordinary `compileArgs` suffix is already
flat. `SaturatedClosureCallResolution.argumentsStructuredFinitePath` combines
that compiler theorem with the existing semantic assembly law: in exactly
`argumentTarget.length` structured steps it leaves the complete physical
callee row on the operand stack, related to the captured and newly supplied
source arguments. The caller supplies neither target syntax nor execution.
The entry composition is now exact as well.
`SaturatedClosureCallSite.semanticArgs_size` exposes the shared source arity
fact, and `SaturatedClosureCallResolution.sourceStageAndEnterFinitePath`
reconstructs the source staging/closure-consumption pair in exactly two
interpreter steps. On the target,
`targetDispatchArgumentsAndEnterFinitePath` composes the matcher fold,
capture/argument assembly, and the real generated `enterCall` step, retaining
the precise call frame and every conditional label. Finally,
`structuredWasmLeaveReplicatedClosureLabelsFinitePath` proves that normal
selected-body fallthrough restores the caller operand tail and continuation
in exactly `before.length + 1` steps. The callee-return boundary is now exact
too. `structuredWasmSaturatedCalleeReturnAndResumeFinitePath` composes the
one-result call return, selected-body result write, complete matcher-label
unwind, and the enclosing generic `let` reload/write pair in exactly
`before.length + 5` target steps. `ConcreteStructuredSaturatedBindFrameFocus`
lifts that control path to the simulation relation: one source bind-frame step
re-enters the recursively compiled continuation with the caller operand tail,
local relation, and frame alignment restored. None of these theorems accepts
an execution certificate. `ConcreteStructuredSaturatedCallEntryFocus` now
connects the exact matcher/argument/call prefix to the generated callee row,
and its entry-relative cache laws recover the saved caller from the recursively
evolved callee store and witness. The hereditary structured induction therefore
admits saturated closure calls recursively, returns through every saved matcher
label, restores the original caller resources, and continues in compiled code.
Program-indexed closure ABI alignment is supplied once at the fixed theorem
entry and transported through cumulative descriptor persistence; it is static
allocation metadata, not target behavior.
`ConcreteSupportedExport.reachesYield_reuseBudgetedStructured_generated` now
constructs the canonical source-code and generated structured-function body
entries from the real supported export and ordinary initial ABI/cache frame.
It returns both exact finite paths, related yield, evolved entry-relative
resources, and endpoint observation agreement without a caller-supplied focus
or target path. This remains explicitly the terminating admitted-fragment
boundary; it is not mislabeled as W6.7f, whose ranked relation must preserve
every finite prefix without a termination premise.
`ConcreteStructuredControlRel` is now the first unified relation component.
Its ten constructors cover ordinary code/yield, pure-external call-ready and
bind-ready states, direct-call argument-ready, callee-entry, and bind-return
states, plus saturated-call staging, callee-entry, and matcher-unwinding
bind-return states. One `observes` theorem discharges exact world/trace agreement for every
constructor. The external protocol is split at individual source-step
boundaries: compiled arguments take their exact generated prefix, the imported
call takes one target step, and the destination write takes one target step.
`ConcreteExternalCallEvidence` is the deliberately orthogonal runtime boundary
consumed by the middle transition; it records the concrete host step, witness
extension, and runtime/result refinement, but is not a main-theorem premise.
`callEvidence_of_budget` now derives that evidence from the existing
Int/Nat/scalar handler laws and the ordinary heap-budget frame. It also
reconstructs the exact residual budget and installed-handler frame.
`advance_call_of_budget`, `advance_call_bind_of_budget`, and
`advance_external_of_budget` progressively hide the internal evidence and
compose the exact imported-call and destination-write steps. The final theorem
matches the source's three-step external protocol against precisely the
production argument prefix followed by two target steps, and re-enters the
adapted continuation with the reduced frame. Saturated closure entry is now
split at its remaining source-step boundary as well.
`advance_saturatedCall_stage` takes the source to `.invokeValue` while the
target path is reflexive, so the unchanged source runtime remains related to
the unchanged concrete store. The new saturated-call-ready focus retains the
compiler-produced dispatch. Its `advance_enter` theorem then consumes the
closure in one source step while independently deriving the complete matcher,
capture/argument, and generated-callee-entry target path from compiler
adaptation plus the cache/ABI frame. It returns the evolved cache frame and
matcher capacity/store transports, without accepting a target program, path,
or candidate-selection certificate. `compilerStructuredControlRank` now
combines the staging phase with recursive silence depth, proving strict descent
for empty-argument staging, persistent ownership erasure, and nested
default-only case erasure. `advance_defaultOnlyCase_ranked` packages that last
zero-target transition locally. The relation-wide per-source-step `advance`
law is now the next proof boundary.
Heap-valued cache misses remain the facts-aware transport redesign after
saturated calls.

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

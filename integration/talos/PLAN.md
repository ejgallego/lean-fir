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

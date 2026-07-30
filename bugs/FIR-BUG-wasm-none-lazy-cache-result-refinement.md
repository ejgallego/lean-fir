---
id: FIR-BUG-wasm-none-lazy-cache-result-refinement
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e7b4813cc4e06543d43b3449588ffb8233f96a3e
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-30
reproduction: Fir/Wasm/WellFormed.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

The supported-source checker admits a precise nullary declaration result
refining a wider call-site result, but lazy-cache lowering types the physical
cache slot from the declaration signature and emits `cacheSet`, `global.set`,
and `global.get` using the call-site kind. The generated symbolic module
therefore fails its own exact global-kind validation.

## Minimal reproduction

Define a nullary declaration whose result type has ABI kind `.object`, then
call it with an LCNF let declaration whose result type has ABI kind `.tobject`.
`supportedNamedCall` accepts the call because `.object.refines .tobject`.

The cache initializer contributes `[.uint32, .object]` to
`Module.cacheGlobalKinds`, while `compileLetValue` emits:

```text
cacheSet declaration .tobject
global.set valueIndex .tobject
global.get valueIndex .tobject
```

`validateModule` rejects the `global.set` or `global.get` because the selected
global has exact kind `.object`.

## Exact commands

```text
make check
make talos-check
```

The W6 contract regression records the admitted refinement and the distinct
declaration/call-site cache kinds.

## Expected semantics

Lazy lowering should preserve the same ABI refinement admitted for ordinary
named calls. The cached physical value should be stored and loaded at the
declaration's actual result kind; that actual kind may then refine the
call-site destination kind.

## Actual behavior

`cachedDeclarationNames` selects the call by name. `cacheGlobalKinds` derives
the value lane from the selected declaration's signature. Independently,
`compileLetValue` derives `resultKind` from the caller's let type and uses it
for the cache runtime operation and both value-global instructions.

`lowerSupported` only runs source validation followed by lowering, so it can
return this inconsistent symbolic module. The production Talos adapter calls
`validateModule` and rejects it as `.invalidGlobalKind`.

## Proof or differential evidence

The cache-table proof needs the declaration signature kind to equal the kind
used by the generated cache operation. That equality is not derivable from
`WasmSupported`: `supportedNamedCall` supplies only
`targetResult.refines callSiteResult`, and `.object.refines .tobject` is a
strict refinement.

## Semantic impact

A program in the advertised supported source domain can lower successfully
but cannot be adapted or emitted. This also prevents the compiler-correctness
proof from constructing a generated cache slot at the operation's claimed
kind without adding a false equality premise.

## Classification and triage

This is a shared lowering/ABI alignment defect. The W6 concrete cache runtime
is already indexed by the operation's exact kind and should not weaken its
slot decoding to accept a differently declared lane.

## Workaround

The W6 proof boundary names exact generated cache-kind alignment explicitly.
It must not claim that the current supported-source predicate establishes
that property.

## Upstream tracking

none

## Resolution and regression

Confirmed. Coordinate a shared lowering change so the lazy-cache sequence uses
the target declaration's actual result kind and exposes its refinement into
the caller's declared destination kind. Then add an executable source
regression in the integration-owned symbolic lowering/validation suite and
derive the W6 alignment boundary from the repaired compiler output.

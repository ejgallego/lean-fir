---
id: FIR-BUG-wasm-none-closure-application-ownership
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-30
reproduction: Fir/Validation/Corpus.lean#mixed-closure-capture-twice
regression: scripts/wasm_semantic_host.mjs
---

# Summary

The semantic Wasm host reads closure captures without implementing Lean's
ownership-transfer boundary for closure application, so applying a shared
closure twice can release heap captures during the first call and fault on the
second.

## Minimal reproduction

Create a closure that captures boxed `USize`, `Float32`, and `Float` values,
retain the closure once, and apply it twice. The generated dispatch first
matches the closure metadata and then projects its fixed arguments. Each
callee unboxes and releases those arguments.

The first semantic-host application releases all three boxes. The second
application reaches `unbox` with the first box already dead.

## Exact commands

Run the fresh float validation case:

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --case mixed-closure-capture-twice \
  --out-dir _build/validation-mixed-closure-twice
```

Native and LCNF agree. The V8 adapter faults with:

```text
SemanticFault: FIR semantic fault: deadObject
    at SemanticHost.unbox
```

## Expected semantics

Opening a closure consumes one reference to it. An exclusive closure transfers
its fixed arguments and becomes dead without recursively releasing them. A
shared closure remains live with one fewer reference and retains each heap
capture once so the callee receives owned arguments. A persistent closure and
its recursively persistent captures require no reference-count changes.

## Actual behavior

`closureMatches` only compares metadata and `closureProj` only reads a fixed
field. Neither operation consumes the closure nor retains captures. The
generated dispatch therefore exposes borrowed references where Lean's
application boundary supplies owned references.

## Proof or differential evidence

The `mixed-closure-capture-twice` native and LCNF observations are identical.
The same compiler-produced Wasm module fails in V8 after the first application
decrements all boxed captures from reference count one to dead.

## Semantic impact

Any repeated application of a closure with heap captures may fault, reuse dead
objects, or disagree with native execution. Immediate-only captures masked the
problem; heap-only floating boxes make it deterministic.

## Classification and triage

This is a shared FIR semantic-contract gap. The integration-owned closure
application contract must define consumption and capture transfer. W7 may
implement the executable adapter behavior, while W6 must separately refine the
concrete matcher/projection protocol to that contract.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. The regression must cover exclusive, shared, and persistent
closures with heap and immediate captures, including repeated application.

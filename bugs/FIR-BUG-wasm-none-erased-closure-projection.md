---
id: FIR-BUG-wasm-none-erased-closure-projection
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-20
reproduction: Fir/Wasm/PrettyFormat.lean#prettyRaw
regression: Fir/Wasm/Examples.lean
---

# Summary

Static closure dispatch projected captured erased parameters through the
semantic host even though erased values have one canonical physical and
semantic representation.

## Minimal reproduction

Lower a compiler-produced closure that captures an erased type-class argument
and is later applied through the closure-dispatch path.

## Exact commands

```sh
lake build Fir.Wasm.Examples
```

## Expected semantics

Closure dispatch synthesizes the canonical erased value (`i32 0`) for an
erased fixed parameter and projects only runtime-relevant captures.

## Actual behavior

`compileFixedClosureFields` emitted `RuntimeOp.closureProj ... .erased`.
`RuntimeOp.abiWellFormed` correctly rejected that operation, so an otherwise
supported `Std.Format.prettyM` closure failed during lowering.

## Proof or differential evidence

After internalizing the ordinary `prettyM` helper closure, lowering reported
28 invalid `closure_proj` operations whose result signatures were
`#[erased]`. No source observation can distinguish the projected value from
the canonical erased value.

## Semantic impact

Compiler-generated closures with erased captures could pass the source support
gate but fail before Wasm encoding.

## Classification and triage

This is a `wasm-adapter` issue: the target adapter attempted to materialize a
source-erased field through a host operation that deliberately has no erased
projection contract.

## Workaround

`compileFixedClosureFields` now emits `i32Const .erased 0` for erased fixed
parameters.

## Upstream tracking

none

## Resolution and regression

Resolved in the Wasm generation lane. A synthetic erased-capture closure
regression guards both the absence of erased closure projections and successful
lowering.

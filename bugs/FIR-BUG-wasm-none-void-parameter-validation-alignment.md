---
id: FIR-BUG-wasm-none-void-parameter-validation-alignment
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 35b5af5c1209885784d187e0349db8c7f1ecbbc9
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-31
reproduction: integration/talos/FirTalos/ConcreteStructuredValidation.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

Production lowering retained source `void` declaration parameters as physical
`.erased` lanes, but supported lowering continued to omit those parameters
from its local-kind row.

## Minimal reproduction

For a declaration containing a source `void` parameter, compare
`Fir.Wasm.addSupportedDeclarationParams?` with
`Fir.Wasm.addDeclarationParams`. The former omitted the parameter while the
latter inserted its fvar with kind `.erased`.

## Exact commands

```text
lake build FirTalos.ConcreteStructuredValidation
```

Before the repair, the validator/lowerer alignment theorem fails at
`addSupportedDeclarationParams?_lowered` because the two folds have different
steps.

## Expected semantics

Supported lowering and production lowering must expose the same physical
declaration-local row. A source `void` parameter remains semantically
unobservable, but it still occupies the erased Lean calling-convention lane
and may occur as a compiler-generated argument.

## Actual behavior

Supported lowering returned the old row unchanged for a `void` parameter;
production lowering inserted `(param.fvarId, .erased)`.

## Semantic impact

Besides invalidating the alignment proof, dropping the validator entry can
make a compiler-generated fvar in a declaration-aware call appear unknown to
supported lowering even though production lowering assigns it a physical
local.

## Proof or differential evidence

The proof of `addSupportedDeclarationParams?_lowered` could not align the
supported and production parameter folds for a source `void` parameter:
supported lowering kept the old row, while production lowering inserted the
parameter at ABI kind `.erased`. The repaired theorem, the focused Talos proof
cone, and the complete interpreter differential gate now pass with the shared
transparent classifier.

## Classification and triage

This is a validator/lowerer contract mismatch introduced when production
lowering began preserving physical void lanes. The correct repair is to use
the shared ABI classifier for every known declaration parameter, including
its `.erased` result for source `void`. Declaration-argument canonicalization
must use that transparent classifier as well, rather than Lean expression
`BEq`, so validator success can constructively imply lowerer success.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`addSupportedDeclarationParams?` now inserts every known declaration
parameter using `declarationParamKind?`. Named-call and partial-capture
canonicalization select source `void` through `abiValueKind?`/
`checkedAbiKind?`, keeping validation and lowering on the same transparent
classification. The executable examples retain the physical void-lane
regression, and the Talos validator/lowerer alignment theorem is forced
through the complete proof cone.

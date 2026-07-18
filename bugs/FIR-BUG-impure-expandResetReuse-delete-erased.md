---
id: FIR-BUG-impure-expandResetReuse-delete-erased
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: expandResetReuse
discovered-by: differential-test
first-seen: 2026-07-18
reproduction: Fir/Validation/Corpus.lean#changeOrGrow
regression: Fir/LeanIR/Runtime.lean#deleteValue
---

# Summary

Lean 4.32's `ExpandResetReuse` can execute `del` on the erased slow-path
sentinel after it rewrites a reset token, but FIR's impure runtime accepts
`del` only for a live heap reference and reports `expectedHeapReference` for
the sentinel.

## Minimal reproduction

`changeOrGrow false` contains a reset followed by a reuse whose replacement is
larger than the original constructor. `ExpandResetReuse` creates a reset join,
passes `.erased` to it when `isShared` is true, and rewrites the original token
decrement in the join body to `del`. The `change == false` arm executes that
`del` independently of the sharing discriminator.

Run the generated declaration with a shared `GrowSwitch.left` cell (reference
count greater than one). The slow path binds the reset parameter to `.erased`
and reaches `deleteValue runtime .erased`.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case reuse-grow-delete \
  --plan validation-plans/native-v8.json \
  --out-dir /tmp/fir-reuse-grow-delete
```

The existing corpus invocation exercises the unique branch. A permanent
shared-input regression must be added before resolving this card.

## Expected semantics

FIR's impure interpreter must agree with the pinned compiler's expanded reset
path for the erased/boxed-zero sentinel. Deleting the failed-reuse sentinel
must have the same no-op behavior as Lean's generated code, while deleting a
live unique constructor must still release that allocation.

## Actual behavior

`deleteValue` pattern-matches only `.object (.heap location)` and otherwise
returns `RuntimeFault.expectedHeapReference`. The Wasm support gate therefore
cannot soundly admit `changeOrGrow`: treating the join parameter as a heap
object would turn the source fault into a target invalid-handle failure, while
admitting the current source behavior would disagree with native Lean.

## Proof or differential evidence

The pinned `ExpandResetReuse.mkSlowPath` passes `.erased` to the reset join.
`processResetCont` rewrites a decrement of the reset token to `.del` before it
expands the reuse. The generated `changeOrGrow` LCNF places that `del` in the
larger-replacement arm outside the later `isShared` case split. FIR's
`deleteValue` definition then rejects the value constructed by the same pass.

## Semantic impact

The interpreter and semantic Wasm ABI do not currently specify the slow
delete path produced by Lean 4.32. Sound program-only Wasm admission for
`reuse-change-tag` and `reuse-grow-delete` must remain closed until the shared
runtime contract is corrected and both tracks rebase on it.

## Classification and triage

This is classified as `fir-semantics`: the discrepancy is between Lean's
compiler-produced final impure program and FIR's shared runtime operation, not
between the Wasm encoder and its host.

## Workaround

Do not admit `changeOrGrow` based only on the current unique-input corpus
invocations. Keep the whole declaration outside `WasmSupported` until the
shared `del` contract has a native/LCNF regression and an integration-owner
change.

## Upstream tracking

none

## Resolution and regression

Open. The integration owner should add a shared-input compiler-generated
regression, settle erased/tagged `del` behavior against Lean 4.32, update the
interpreter and semantic Wasm host contract together, and then rebase both
feature tracks before Wasm admission continues.

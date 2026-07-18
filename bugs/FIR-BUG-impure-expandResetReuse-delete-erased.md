---
id: FIR-BUG-impure-expandResetReuse-delete-erased
status: fixed
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

`changeOrGrowShared false value` retains `value` while calling
`changeOrGrow false value`, forcing Lean's ownership lowering to pass a shared
`GrowSwitch.left` constructor. `ExpandResetReuse` creates a reset join, passes
`.erased` to it when `isShared` is true, and rewrites the original token
decrement in the join body to `del`. The `change == false` arm executes that
`del` independently of the sharing discriminator.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case reuse-grow-delete-shared \
  --plan validation-plans/native-lcnf.json \
  --out-dir /tmp/fir-reuse-grow-delete-shared
```

## Expected semantics

FIR's impure interpreter must agree with the pinned compiler's expanded reset
path for the erased/physical-zero sentinel. Deleting the failed-reuse sentinel
must have the same no-op behavior as Lean's generated code, while deleting a
live unique constructor must still release that allocation. This is a
delete-specific exception; it does not make `.erased` refine `.object`
globally.

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
larger-replacement arm outside the later `isShared` case split. Before the
fix, `reuse-grow-delete-shared` executed `inc`, `fap`, `cases`, `join`,
`isShared`, `jump`, and `del`, then faulted with `expectedHeapReference`;
native Lean returned the retained `left 7` and new `big 7 7` pair. Lean's C
emitter maps `del` to `lean_del_object`, and the native run confirms that the
physical-zero operand is a no-op.

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

none

## Upstream tracking

none

## Resolution and regression

Resolved by making `deleteValue runtime .erased` return the unchanged runtime
and retaining the previous heap-delete and invalid-nonsentinel behavior.
`reuse-grow-delete-shared` is the permanent compiler-generated native/LCNF
regression.

The Node/V8 semantic host recognizes physical zero only in its `delete`
operation. The proof-facing Talos host mirrors this with `decodeHostArgs` and
`hostStep_delete_erased`; `decodeArgs_object_handle_ne_reserved` preserves the
ordinary heap-only object theorem. `AbiKind.object`, generic handle decoding,
and other object operations remain unchanged.

Generation must now admit `del` as a safe use of the guarded erased join
parameter before the case can reach V8. W6 must mirror the new source contract
by treating concrete word zero as a no-op in `deleteObject`. Both are consumer
adaptations to this fixed shared contract, not local semantic workarounds.

---
id: FIR-BUG-wasm-none-constructor-allocation-tag-truncation
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-16
reproduction: Fir/Wasm/WellFormed.lean#supportedLetDeclKind?
regression: none
---

# Summary

The supported Wasm fragment bounds constructor tags on case alternatives but
not on constructor allocations. An allocated tag outside `UInt32` can
therefore truncate to the same `i32` value as an in-range alternative and
select the wrong branch.

## Minimal reproduction

Allocate a constructor whose `CtorInfo.cidx` is `UInt32.size`, then case split
on it with a single constructor alternative whose tag is zero and an
observable default branch. `supportedLetDeclKind?` accepts the allocation and
`supportedAlt` accepts the alternative. Source evaluation takes the default;
the semantic Wasm host returns `UInt32.ofNat UInt32.size = 0`, so generated
Wasm takes the constructor alternative.

## Exact commands

From the repository root:

```sh
rg -n "ctor info args|constructorTagFitsI32|UInt32.ofNat tag" Fir/Wasm/WellFormed.lean Fir/Wasm/Lower.lean integration/talos/FirTalos/Runtime.lean
lake build Fir.Wasm.Examples
```

## Expected semantics

Every constructor value admitted by `WasmSupported` has a tag whose target
representation is injective for every generated constructor-case comparison.

## Actual behavior

Only `supportedAlt` and the alternative side of `compileCaseChainWith` check
`constructorTagFitsI32`. Constructor allocation accepts and preserves an
unbounded source `Nat` tag, while `getTag` narrows that tag to `UInt32`.

## Proof or differential evidence

The W4 proof of the generated `getTag; i32.const; i32.eq; if` sequence requires
recovering equality of source constructor tags from equality of their
`UInt32.ofNat` images. The alternative bound supplies only one of the two
range premises; the allocated discriminator has no corresponding invariant.

## Semantic impact

`lowerSupported` can accept a program whose source and target select different
case branches. This invalidates the intended W4 theorem domain even though the
earlier alternative-tag truncation regression remains rejected.

## Classification and triage

This is a Wasm-adapter supported-fragment defect. FIR consistently stores and
compares constructor tags as `Nat`; the discrepancy is introduced by the
semantic Wasm `i32` tag boundary.

## Workaround

None. Record the discrepancy before strengthening the supported-fragment and
general-lowering constructor-allocation checks.

## Upstream tracking

none

## Resolution and regression

Pending a negative supported-fragment and general-lowering fixture whose
allocation tag is out of range while every case alternative remains in range.

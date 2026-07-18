---
id: FIR-BUG-wasm-none-handwritten-scalar-layout
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-18
reproduction: Fir/LeanIR/InterpreterExamples.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

The hand-built mixed-layout mutation fixture uses an `sproj`/`sset` scalar-base
operand that disagrees with Lean 4.32's final-impure `ToImpure` contract.

## Minimal reproduction

`layoutInfo` declares one object field and one `USize` field. `mutationCode`
then uses `.sset p 1 0 ...` and `.sproj 1 0 p`; the first layout operand is
`1`, although the compiler-generated value for that constructor is
`layoutInfo.size + layoutInfo.usize = 2`.

## Exact commands

From the repository root, run:

```text
lake build Fir.LeanIR.InterpreterExamples Fir.Wasm.Concrete.Examples
```

Then compare the fixture with Lean 4.32's
`Lean/Compiler/LCNF/ToImpure.lean`: `lowerProj` emits
`.sproj (ctorInfo.size + ctorInfo.usize)`, and constructor initialization emits
the same sum in `.sset`.

## Expected semantics

The first scalar-layout operand counts every fixed-width semantic slot before
the packed scalar region. For a constructor with `size = 1` and `usize = 1`,
it is `2`; byte offset `0` then selects the first packed scalar byte.

## Actual behavior

The hand-built FIR interpreter fixture uses `1`. It still passes because the
semantic runtime stores scalar fields by the literal `(width, offset)` key and
does not validate that key against constructor metadata.

## Proof or differential evidence

`ConstructorLayout.scalarFieldOffset?` implements the Lean 4.32 formula and
the concrete regression proves that operand `2` maps to byte offset `48`,
while operand `1` is rejected for the same mixed constructor. The upstream
`ToImpure` source independently fixes the generated operand to
`ctorInfo.size + ctorInfo.usize`.

## Semantic impact

The shared mutation example is not a faithful final-impure compiler snapshot.
It cannot be used unchanged to validate a concrete memory runtime, because a
runtime honoring compiler layout would reject the scalar access. No
compiler-produced program is known to be affected.

## Classification and triage

This is a FIR fixture-model discrepancy. The concrete layout and Lean 4.32
compiler agree; the permissive semantic interpreter makes the malformed
hand-written fixture observationally succeed.

## Workaround

W6 concrete-runtime fixtures use the compiler-shaped operand `size + usize`.
The shared example remains unchanged until the integration owner coordinates
its correction.

## Upstream tracking

none

## Resolution and regression

unresolved

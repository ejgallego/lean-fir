---
id: FIR-BUG-wasm-none-settag-uint32-admission
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-14
reproduction: Fir/Wasm/WellFormed.lean
regression: integration/talos/FirTalos/ConcreteStructuredValidation.lean
---

# Summary

Production validation accepts `.setTag objectId tag continuation` for every
`Nat` tag, while the concrete wasm32 runtime stores the tag through `UInt32`
and its refinement theorem correctly requires `tag < UInt32.size`.

## Minimal reproduction

Construct otherwise supported impure LCNF containing
`.setTag objectId UInt32.size continuation`. `supportedCodeWithJoins` checks
only that `objectId` has kind `.object` and that the continuation is supported.
The source interpreter stores the full natural tag; `setTagStep` writes
`UInt32.ofNat tag`, which wraps this value to zero.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteStructuredValidation
```

Inspect the `.setTag` branch of `Fir.Wasm.supportedCodeWithJoins`,
`Fir.LeanIR.Impure.setTag`, `FirTalos.Concrete.setTagStep`, and
`ConstructorTagEffectSupported.setTag`.

## Expected semantics

The supported compiler domain should reject constructor-tag mutations that do
not fit the concrete 32-bit header, just as constructor allocation and case
validation already reject unrepresentable tags. A successful validation should
therefore imply `tag < UInt32.size`.

## Actual behavior

The raw lowering domain admits an unrepresentable semantic tag. Source
execution succeeds with the full `Nat`, while concrete execution truncates the
tag modulo `UInt32.size`; the existing mutation refinement cannot be applied.

## Proof or differential evidence

`ConcreteStructuredValidationFocus.setTagContinuation` can invert the exact
production validator but exposes no range premise. The sound
`ConstructorTagEffectSupported.setTag` constructor and
`setTagStep_of_refines_with_capacity` both require `tag < UInt32.size`, so a
validator-derived current-step admission theorem is impossible for the
accepted out-of-range node.

## Semantic impact

For raw supported LCNF, later tag observation or case selection can distinguish
source execution from generated Wasm. Normal compiler output is expected to
use constructor indices that fit, but that phase fact is not retained by this
validation branch.

## Classification and triage

This is a compiler-admission defect. Add the direct `UInt32` range check to the
production `.setTag` validator and a negative regression for the boundary
value. Do not weaken the concrete header relation or silently model source tags
modulo `2^32`.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The isolated shared contract `982ed402` requires
`decide (tag < UInt32.size)` in the production `.setTag` validator. The
boundary value `UInt32.size` is now rejected by both `supportedProgram` and
`lowerSupported`, while existing compiler-generated tags remain accepted.

`ConcreteStructuredValidationFocus.setTag_eq` extracts the exact width and
ordinary-object-local facts from that validator. A successful source-step
inversion exposes the heap location, live constructor cell, and semantic
update; `admit_setTag_of_step` combines only those facts into the existing
`ConstructorTagEffectSupported` judgment. The aligned theorem therefore
derives constructor-tag current-step admission without weakening the concrete
header relation or inspecting target execution.

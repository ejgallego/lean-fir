---
id: FIR-BUG-wasm-none-scalar-field-layout-admission
status: confirmed
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

Production validation checks the object local, scalar payload ABI, source type
annotation, and supported scalar family for `.sset`, but does not check that
the encoded slot and byte coordinates select a valid, non-overlapping packed
region of the refined constructor descriptor. The source interpreter accepts
the same unchecked coordinates, while the sound concrete mutation theorem
requires exact layout and separation facts.

## Minimal reproduction

Construct otherwise supported raw impure LCNF with a live constructor whose
descriptor has no scalar bytes, then execute a `UInt64` `.sset` at that
constructor's packed-slot coordinate and byte offset zero. The `.sset` branch
of `supportedCodeWithJoins` accepts the object local and annotated `UInt64`
payload without retaining the constructor descriptor or checking `ssize`.

An overlapping write can likewise be formed by first installing one scalar
field and then writing a differently sized field whose byte range overlaps it
at a distinct coordinate. Source `setScalarField` filters only an identical
`(slotIndex, byteOffset)` pair, so both semantic entries remain.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteStructuredValidation
```

Inspect the `.sset` branch of `Fir.Wasm.supportedCodeWithJoins`, source
`setScalarField`, `ScalarFieldMutationSafe`, and
`ScalarFieldEffectSupported.sset`.

## Expected semantics

The supported compiler domain should establish that the scalar slot equals
the constructor's packed-region start, the selected scalar width fits within
`CtorInfo.ssize`, and the new byte range is disjoint from every retained
semantic scalar field. This may be derived from a preserved source typing and
layout invariant or checked by an equivalent validator analysis.

## Actual behavior

Validation ignores both numeric `.sset` coordinates. Successful source
execution proves only that the object is a live constructor and the payload is
a scalar; it accepts every natural slot and byte offset. Consequently neither
validation nor a source step proves the layout premises required by concrete
memory refinement.

The validator also admits `Float32` and `Float`. That is a separate proof
coverage boundary: the current `ScalarFieldMutationSafe` and concrete write
theorems cover only the four packed integer ABI kinds. This card does not
claim that generated float stores are operationally incorrect.

## Proof or differential evidence

`ConcreteStructuredValidationFocus.sset_eq` extracts exactly the object lane,
payload lane, matching annotation, and supported scalar-family guard from the
production validator. `ConcreteStructuredCodeFocus.sset_source_of_step`
extracts exactly the scalar payload, live constructor, and semantic update
from a successful source step. Neither result contains coordinate bounds or
non-overlap evidence.

`ConcreteScalarFieldLayoutAligned` isolates the remaining source/runtime
typing fact. Under that boundary,
`ConcreteStructuredValidationFocus.admit_sset_of_step` constructs the existing
`ScalarFieldEffectSupported` judgment without inspecting target execution or
storing a translation certificate.

## Semantic impact

An out-of-bounds packed write can address bytes outside the constructor's
declared scalar region. An overlapping write can change concrete bytes used by
another retained semantic scalar entry, violating `ConstructorObjectRel` even
though source execution keeps both entries. Raw LCNF accepted by FIR can
therefore fall outside the concrete compiler-correctness domain.

Upstream Lean-generated LCNF is expected to provide coherent coordinates, but
FIR's accepted raw-LCNF domain currently does not state or verify that fact.

## Classification and triage

This is a compiler-admission defect. Prefer one preserved source layout
judgment covering constructor creation, reuse, aliases, joins, and calls, or an
equivalent executable validator analysis. Do not weaken concrete bounds or
silently discard overlapping semantic fields.

The Float32/Float proof extension should remain a separate W6 refinement
slice unless it reveals an implementation discrepancy.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Pending. The proof-side `ConcreteScalarFieldLayoutAligned` boundary documents
the minimal missing invariant and permits explicit well-typed-source
refinement experiments; it does not repair production admission by itself.

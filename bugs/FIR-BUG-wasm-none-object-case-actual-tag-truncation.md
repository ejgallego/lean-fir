---
id: FIR-BUG-wasm-none-object-case-actual-tag-truncation
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-30
reproduction: integration/talos/FirTalos/ConcreteRuntime.lean#getTagStep
regression: unresolved
---

# Summary

The generated object-case ABI narrows the successful semantic `getTag` result
to `UInt32` before comparing it with a constructor alternative.  Production
validation bounds every compared constructor tag and every compiler-created
constructor tag, but the ordinary object relation also admits promoted tagged
values whose payload uses the full `UInt64` range.  An actual tag outside the
`UInt32` range can therefore wrap to an in-range alternative and select a
different branch from final-LCNF semantics.

## Minimal reproduction

Use an object-case discriminator related to the promoted tagged payload
`UInt32.size`, a constructor alternative with tag zero, and an observable
default branch.  Source `getTag` returns `UInt32.size` and selects the default;
`getTagStep` returns `UInt32.ofNat UInt32.size = 0`, so generated Wasm selects
the constructor branch.

## Exact commands

```text
rg -n "UInt32.ofNat tag.toNat|actualFits : actualTag < UInt32.size" \
  integration/talos/FirTalos/ConcreteRuntime.lean
lake build Fir.Wasm.Concrete.ProjectionCorrectness
```

Inspect `getTagStep`, `getTagStep_of_refines`, and
`LiveHeapRel.tobjectTag_lt_uint64`.

## Expected semantics

Every accepted object-case test preserves equality between the exact semantic
tag and each compared constructor tag for every value admitted by the ordinary
source/target relation.

## Actual behavior

The concrete decoder returns a `UInt64`, but the imported and resident helper
ABI narrows it to `UInt32` before the generated comparison.  The proof can
relate this comparison to source equality only under the additional
`actualTag < UInt32.size` premise.

## Proof or differential evidence

`LiveHeapRel.readTag_tobject_refines` proves that the concrete decoder returns
`UInt64.ofNat actualTag`, but `getTagStep_of_refines` requires the extra premise
`actualTag < UInt32.size` before narrowing that result.  The compiler-derived
current-node admission campaign cannot derive this premise from
`ConcreteRuntimeRel`: `TaggedReferenceRel.promoted` intentionally represents
arbitrary `UInt64` payloads.

The strongest relation-derived fact is instead
`LiveHeapRel.tobjectTag_lt_uint64`.  Heap constructors satisfy the stronger
`UInt32` bound through their concrete header; immediate and promoted tagged
references satisfy the exact `UInt64` bound.

## Semantic impact

Without an additional source invariant, the accepted final-LCNF-to-Wasm
relation does not preserve case selection for every related object value.  A
caller-supplied tag-range invariant masks the discrepancy but cannot be
derived from compiler validation or the existing runtime relation.

## Classification and triage

This is a Wasm adapter and runtime-operation ABI discrepancy.  Do not weaken
the full-width tagged reference relation or add an arbitrary caller invariant
to make the narrowing proof go through.

## Workaround

The current W6 compatibility theorem accepts a source invariant that proves
the current discriminator tag fits `UInt32`.  This is sound but is not a
compiler-derived public theorem and therefore remains outside the intended W6
endpoint.

## Upstream tracking

none

## Resolution and regression

Make the generated case-test boundary preserve the exact successful tag, for
example by returning an `i64` from the imported/resident `getTag` helper and
comparing it with an exact `i64` constructor constant.  An equivalent checked
high-word scheme is acceptable.  The resolution must cover both the abstract
host and the Wasm-resident helper and remove the dynamic `UInt32` premise from
the generic object-case simulation.

The future regression must execute a promoted payload equal to `UInt32.size`
against a zero constructor alternative and observe the source-selected default
through both imported-host and resident-runtime artifacts.

### Relation to earlier work

`FIR-BUG-wasm-none-constructor-allocation-tag-truncation` remains fixed: its
validator check prevents the compiler from allocating an oversized
constructor tag.  This card is distinct because the actual case discriminator
may enter through a tagged/promoted value rather than a constructor
allocation.

---
id: FIR-BUG-wasm-none-natural-validator-refinement-admission
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: eca10875e2a8513d90e887ccc83a6b22a551c9fa
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-23
reproduction: Fir/Wasm/Concrete/HeapRefinement.lean
regression: Fir/Wasm/Concrete/HeapRefinement.lean
---

# Summary

The W6 `LiveHeapRel` Natural case admits decoded heap objects that the
resident `validateNatural` helper rejects, so the relation is not currently
strong enough to prove the public checked `Nat.add` path cannot trap.

## Minimal reproduction

`LiveCellRel.natural` and `NaturalObjectRel` constrain the object kind,
big-Natural marker, extent, limb capacity, decoded mathematical value, and
ownership fields. They do not constrain reserved header fields or require a
canonical most-significant limb. Consequently the relation admits, for
example, a two-limb Natural whose top limb is zero and whose lower limb
decodes to the semantic value.

`Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction` deliberately
rejects that representation through `requireReservedZero` and
`requireTopNonzero`. It also enforces the promoted-versus-big boundary for a
one-limb ordinary object. The public checked `Nat.add` body calls this
validator before its count, carry, allocator, and writer helpers.

## Exact commands

```sh
rg -n "LiveCellRel.*natural|structure NaturalObjectRel|requireTopNonzero|requireReservedZero|naturalBigValidation" \
  Fir/Wasm/Concrete/HeapRefinement.lean \
  Fir/Wasm/Concrete/NaturalAllocationCorrectness.lean \
  Fir/Wasm/Emit/ResidentBigNumeric.lean
```

The proof obstruction appears when composing
`wp_checkedNatAddPrefixProgram` from `LiveHeapRel`: the relation supplies the
decoded value but cannot establish successful `validateNatural` calls.

## Expected semantics

Every concrete Natural admitted by the public compiler simulation relation
must satisfy the resident Natural validator, including its reserved-field,
top-limb, ownership, and promoted-versus-big representation checks.

## Actual behavior

The refinement relation admits a strict superset of validator-accepted
Natural layouts. A related source state can therefore correspond to a target
state that traps in validation before executing otherwise proved arithmetic.

## Proof or differential evidence

The exact generated multi-limb producer theorem is complete after validation:
it derives count/limb arithmetic, allocation, writer execution, carry stores,
heap extension, and typed return. Composing the preceding public checked
prefix exposes validator success as the only condition not derivable from the
current Natural refinement relation. The missing fields are semantically
observable because the generated validator branches on them.

## Semantic impact

An unconditional public `Nat.add` simulation theorem from `LiveHeapRel` would
be unsound with the current relation. The same weak Natural case may affect
every checked arbitrary-precision helper that begins with
`validateNatural`.

## Classification and triage

This is currently classified as a W6 refinement-contract defect rather than
a resident-runtime bug. The validator's rejection rules encode the canonical
layouts produced by the runtime. W6 should expose and preserve precisely
those admission invariants, preferably through one reusable relation shared
by all checked Natural helpers.

## Workaround

None. Proofs must not assume successful validation independently of a
representation invariant. A temporary theorem may take an explicit canonical
admission premise, but the ultimate public simulation theorem must derive it
from the strengthened heap relation.

## Upstream tracking

none

## Resolution and regression

Fixed in the W6 Natural-admission invariant slice. `NaturalValidatorAdmission`
now lives with the heap refinement contract, and `LiveCellRel.natural` carries
that admission directly instead of only a decoded `NaturalObjectRel`.
`LiveHeapRel.naturalValidatorAdmission` is the proof-level regression: every
mapped live semantic Natural exposes the exact canonical admission required by
the installed validator. Canonical allocation establishes the invariant, while
reference-count, ownership, persistence, mutation, reset/reuse, framing, and
fault transitions preserve it.

The exact generated validator theorem
`terminatesWith_validateNatural_of_naturalAdmission` therefore composes with
the compiler-facing heap relation without a trusted caller premise. The
resident result writer separately requires its arithmetic producer to prove
that the newly emitted result limbs are canonical; mere equality of decoded
numeric values is intentionally not accepted as a substitute.

---
id: FIR-BUG-impure-none-mixed-reset-child-sharing
status: closed-not-a-bug
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-26
reproduction: Fir/Validation/DirectLCNF.lean
regression: Fir/Validation/DirectLCNF.lean#machine-reset-erased-and-owned-fields
---

# Summary

A direct mixed-field reset fixture reports the retained child as shared under
native Lean but exclusive under FIR's final-impure LCNF interpreter.

## Minimal reproduction

Create a heap child and retain one reference locally. Store a second reference
behind an erased slot in a mixed constructor, consume that owner while
constructing a replacement, and query the retained child's sharing state. The
direct LCNF candidate spells out `inc`, `reset`, `reuse`, and `isShared`.

## Exact commands

From the validation worktree:

```sh
make validate-direct-lcnf
```

The retained evidence run is
`98ac32067689fd0b96684c91b9dce237c2d8a11000f5c8ecb19e15cb74be2884`
with evidence identity
`660c8b88aedeb96dd185c73e2029f1ec0400cbcec081eb5f0cf7398d241dd73c`.

## Expected semantics

Both executions should expose the same post-consumption reference count. If
the mixed owner releases its child reference, the retained child is exclusive
and the fixture returns `73`; otherwise it remains shared and returns `74`.

## Actual behavior

The native backend returns `74`; the direct LCNF interpreter returns `73`.
Both backends terminate successfully, and the other three direct cases remain
equal.

## Proof or differential evidence

The matrix compares all four cases and reports exactly one unequal
`direct-native -> direct-lcnf` observation. The candidate executes the pinned
trace
`lit, lit, ctor, inc, erased, lit, ctor, reset, lit, reuse, oproj, isShared,
cases, return`.

Generated C for the failing fixture represents the native child as a static
constructor with reference count zero. After making the noinline native helper
consume a live `Nat` parameter and making its replacement retain an old-owner
projection, generated C allocates the child and owner, increments the retained
child reference, executes Lean's reset/reuse fast path, releases the owner's
child field, and only then queries exclusivity. Both backends return `73`.

## Semantic impact

If the fixture is equivalent, mixed erased/owned constructor reset has the
wrong child-release semantics in one backend. If it is not equivalent, direct
native-oracle infrastructure needs a guard against static lifting of
reference-count-sensitive values.

## Classification and triage

This is not a Lean or FIR semantics bug. The initial native fixture was not
equivalent to the direct LCNF program: Lean correctly lifted a closed
constructor to persistent storage, while the LCNF program explicitly allocated
an ordinary reference-counted constructor.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The permanent direct fixture passes `41` through a noinline helper parameter
that participates in child construction. This prevents closed-value static
lifting while still letting the real native compiler own allocation, reset,
reuse, and reference-count behavior.

The successful strengthened run is
`e113873e637679df576d7b5db3ed64afa5af218f247254271f3b91a8845fa9e5`
with evidence identity
`fd6035b21c72fba08ce73afd03d5a7c9cafbccb5bf883a5fdd1cf3ff01bdc100`.
All four direct native/interpreter comparisons are equal.

---
id: FIR-BUG-wasm-none-concrete-validation-tagged-ctor-field
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-11
reproduction: integration/talos/artifact/check-concrete-validation-products.mjs
regression: integration/talos/artifact/check-concrete-validation-products.mjs
---

# Summary

The complete Talos artifact gate cannot decode one newly admitted concrete
validation product because a constructor object-field contains the immediate
word `59`, while the concrete host unconditionally decodes every constructor
object-field at the narrower `object` kind.

## Minimal reproduction

Generate the current `native-lcnf-v8-scalars` validation matrix and replay its
shared semantic Wasm products through the concrete host.

## Exact commands

```sh
make validate-v8
node integration/talos/artifact/check-concrete-validation-products.mjs \
  _build/validation-v8
```

## Expected semantics

Every product admitted by `concreteValidationBlockers` should decode to the
same semantic observation as the canonical V8 result, including constructor
fields whose source layout permits tagged values.

## Actual behavior

The native/LCNF/V8 triangle passes all 649 cases and all 1,947 comparisons.
The subsequent concrete-host replay of
`recursive-release-leaf-unique-reuse` aborts while decoding a constructor
field:

```text
WasmAssertionError: concrete word 59 does not refine object
```

The same failure reproduces with the concrete-host code at `main` commit
`1fc7982e`, so it is independent of the W7 resident Array/String helper stack.

## Proof or differential evidence

The canonical V8 result exists and agrees bit-for-bit with native Lean and the
LCNF interpreter. The failure is in the additional concrete-layout observer,
before its observation can be compared with that canonical result.

## Semantic impact

The complete W7 artifact gate is red on an otherwise accepted compiler corpus,
and the concrete validation bridge cannot witness the affected heap graph.

## Classification and triage

This is initially classified as a validation/concrete-decoder mismatch. The
next diagnostic step is to identify the exact case and compare its final-LCNF
field kind, emitted manifest, concrete header, and canonical semantic heap.
No admission fence or representation weakening is authorized.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ConcreteHost.objectSet` now updates the validation-only constructor descriptor
with the physical kind of the value written by the mutation. This matches the
untyped runtime slot: after a valid `tobject` mutation, the same slot may contain
either a heap address or an immediate tagged word, regardless of the kind used
when the storage was first allocated.

`test-concrete-initial-runtime.mjs` allocates an object-only constructor field,
mutates it to an immediate `tobject`, and checks the complete observed object.
The full shared-product replay retains
`recursive-release-leaf-unique-reuse` as the end-to-end regression.

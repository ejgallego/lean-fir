---
id: FIR-BUG-validation-none-array-nested-alias-manifest
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: validation
pass: none
discovered-by: differential-test
first-seen: 2026-08-14
reproduction: Fir/Validation/Corpus.lean#repeatedByteArrayChildArraySetShared
regression: scripts/test_validate_interpreters.py
---

# Summary

The Python corpus-manifest validator rejects nested aliases below an Array
argument even though the protocol and Lean validator define Array and List
paths over the same backend-neutral `seq` datum shape.

## Minimal reproduction

Declare one argument with schema `.array .bytes`, two equal byte-array elements,
and a nested alias from child zero to child one. The generated protocol-v3 JSON
uses:

```json
{
  "argSchemas": [{"array": {"element": "bytes"}}],
  "args": [{"seq": {"value": [
    {"bytes": {"value": [0]}},
    {"bytes": {"value": [0]}}
  ]}}],
  "nestedArgumentAliases": [{
    "source": {"argument": 0, "children": [0]},
    "target": {"argument": 0, "children": [1]}
  }]
}
```

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --case repeated-byte-array-child-array-set-shared \
  --out-dir _build/validation-s11-array-alias-probe
```

## Expected semantics

`ValidationSchema.array` and `ValidationSchema.seq` both accept a
`ValidationDatum.seq`. `resolveArgumentPathChildren` in the Lean protocol
therefore descends through either schema and validates that the two ByteArray
children may share one runtime identity.

## Actual behavior

The native manifest passes all Lean `checkNestedArgumentAliases` guards, but
`scripts/validation_harness.py::_resolve_argument_path` recognizes only the
`{"seq": ...}` schema variant. It aborts before backend selection with
`source: child 0 descends through a non-container`.

## Proof or differential evidence

The emitted descriptor contains `.array .bytes`, two equal `.bytes` datums,
and the canonical `0/[0] -> 0/[1]` alias. Replacing only the schema constructor
with `.seq .bytes` reaches the already-covered List path, demonstrating that
ordering, fixture equality, and child bounds are not the cause.

## Semantic impact

The generic validation infrastructure cannot materialize identity graphs
inside Arrays. Consequently, differential tests cannot combine Array
copy-on-write with repeated heap children supplied at the native-oracle
boundary.

## Classification and triage

This is a validation-harness mirror drift: the Lean protocol is authoritative
and already handles both container schemas. The Python parser needs the same
two-schema branch while retaining the shared `seq` datum validation.

## Workaround

None. Recasting an Array fixture as a List would change the source ABI and the
runtime operations under test.

## Upstream tracking

none

## Resolution and regression

Resolved by teaching `_resolve_argument_path` to descend through both `array`
and `seq` schemas while continuing to require the shared `seq` datum shape.
`test_manifest_nested_argument_alias_contract` now parses the Array form and
preserves its alias descriptor.

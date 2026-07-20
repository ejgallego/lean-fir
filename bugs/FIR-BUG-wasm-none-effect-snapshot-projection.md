---
id: FIR-BUG-wasm-none-effect-snapshot-projection
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-20
reproduction: Fir/Validation/Corpus.lean#recordByteArrayTwice
regression: integration/talos/artifact/test-semantic-host.mjs
---

# Summary

The V8 validation adapter rejected corpus effect projections and retained no
event-time heap snapshots from which to decode mutable external arguments and
results.

## Minimal reproduction

Compile and execute `effect-record-byte-array-twice`. Both external calls
consume and return the same unique byte-array location, first changing byte
zero from `0` to `1` and then from `1` to `2`.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case effect-record-byte-array-twice \
  --plan validation-plans/native-v8-scalars.json \
  --out-dir _build/validation-v8-effects
```

## Expected semantics

The V8 observation should contain two ordered `validation.recordByteArray`
effects. Their argument/result byte arrays must be respectively `0 → 1` and
`1 → 2`, even though the semantic values refer to one mutating heap location.

## Actual behavior

The runner stopped before instantiation with an assertion that every selected
case have an empty `effectProjections` array. The host's public trace retained
only heap references, which would expose final rather than event-time contents
if decoded after execution.

## Proof or differential evidence

Native Lean and the FIR LCNF interpreter agree on the two ordered effects and
their original, intermediate, and final byte arrays. The former V8 adapter
omitted the case instead of producing a comparable observation.

## Semantic impact

Compiler-produced Wasm using validation-owned controlled externals could not
participate in native-to-V8 differential testing. Heap-mutating effects could
not be reconstructed correctly from the final runtime alone.

## Classification and triage

This is a `wasm-adapter` issue. The backend-neutral projection metadata and
LCNF snapshot semantics were already defined; the V8 host/runner had not yet
implemented their consumer side.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The semantic host now retains a private immutable before/after heap view for
each successful external call while keeping its public trace unchanged. The
V8 adapter decodes only declared projections against those views, in call
order, and exact handlers model both validation-owned externals. The semantic
host regression checks two mutations of one location; `effect-record-nat`,
`effect-record-twice`, and `effect-record-byte-array-twice` are permanent
native-to-V8 differential cases.

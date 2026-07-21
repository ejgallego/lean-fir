---
id: FIR-BUG-impure-none-cached-heap-persistence
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-21
reproduction: integration/talos/artifact/call-pretty-format.mjs
regression: integration/talos/artifact/call-pretty-format.mjs
---

# Summary

The FIR interpreter and semantic Wasm host cache a heap result from a
zero-argument declaration without making the cached cell persistent. Generated
LCNF treats that result as persistent, so reset/reuse may mutate or release the
cell and a later cache hit returns a dead object.

## Minimal reproduction

Generate the `Std.Format.prettyM` artifact, instantiate it with an empty
semantic runtime, and render a standalone group containing
`"left" ++ line ++ "right"` at width 80. The pretty printer's
`spaceUptoLine` helper evaluates its cached `_closed_0 : SpaceResult` more than
once.

## Exact commands

```sh
integration/talos/artifact/check.sh
```

The focused reproducer is:

```sh
node integration/talos/artifact/call-pretty-format.mjs \
  integration/talos/artifact/_build/source-pretty-format.wasm
```

## Expected semantics

After a zero-argument declaration is evaluated, a heap value retained in the
declaration cache is persistent. Persistent increments and decrements in final
LCNF are no-ops, and `isShared` must prevent destructive reuse of the cached
cell.

## Actual behavior

`Fir.LeanIR.Impure.RuntimeState.setGlobal` inserts only the value into
`runtime.globals`; it leaves the referenced heap cell at `persistent = false`
and `rc = 1`. The JavaScript semantic host's `cacheSet` operation mirrors that
behavior. `isShared` therefore returns false, reset/reuse mutates and releases
the cached `SpaceResult`, and the next object projection faults with
`deadObject`.

## Proof or differential evidence

The V8 import trace has this decisive suffix:

```text
cacheSet(_private.Init.Data.Format.Basic.0.Std.Format.spaceUptoLine._closed_0)
isShared(cached SpaceResult) = false
... mutate cached field ...
dec(cached SpaceResult)
objectProj(cached SpaceResult) = deadObject
```

The failing handle resolves to the same heap location installed by
`cacheSet`; immediately before the projection its cell has `rc = 0`,
`persistent = false`, and `live = false`. The input group can also be selected
directly from the Lean-produced all-constructor manifest, excluding a
JavaScript heap-layout error.

## Semantic impact

Any nullary compiler declaration returning a heap object can expose a mutable
or dangling cached value. Small fixtures may pass when they read the cached
object only once, so one-shot differential coverage does not rule out the
fault. The semantic interpreter, host-backed Wasm artifacts, and W6 cache
refinement must agree on the corrected persistence transition.

## Classification and triage

This is a shared FIR runtime-semantics issue, not a `prettyM` adapter or Wasm
encoding issue. The integration owner owns the interpreter/runtime change;
the generation lane owns the external-engine reproduction.

## Workaround

None. Marking cached cells persistent only in the JavaScript host would make it
disagree with the shared FIR interpreter, so the artifact lane deliberately
does not apply a host-only repair.

## Upstream tracking

none

## Resolution and regression

Unresolved. The checked JavaScript client retains an explicit expected-failure
assertion for the standalone group. Once the shared cache transition and both
runtime implementations are updated together, that assertion should become a
successful rendering check for both width 80 and width 5.

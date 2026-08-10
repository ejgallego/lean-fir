---
id: FIR-BUG-wasm-none-resident-closure-application-transfer
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-10
reproduction: integration/illuminate-hit-scene/package-smoke.mjs
regression: Fir/Wasm/Emit/ResidentRuntime.lean
---

# Summary

The Wasm-resident closure matcher and projection helpers do not implement the
closure-application ownership transfer already required by FIR's semantic and
concrete runtime contracts. Repeated calls through a shared closure can
therefore unbox a capture that the first call has released.

## Minimal reproduction

Compile `Illuminate.HitScene.query` from Illuminate commit
`af088e313eaade90be100aeaf63ddac79a8c1710` into a zero-import resident module
and run the canonical 301-query HitScene fixture. The first stroke traversal
reuses a closure capturing the boxed stroke width. Its first invocation
releases that box; its second invocation reaches `fir_float_unbox` with the
same capture already dead.

## Exact commands

```sh
cd integration/illuminate-hit-scene
FIR_ALLOW_DIRTY_PACKAGE=1 node package.mjs
```

## Expected semantics

A successful application consumes one closure reference. An exclusive closure
transfers its captures and becomes canonically dead without recursively
releasing them. A shared closure loses one parent reference and retains every
owned heap capture for the callee. A persistent closure is unchanged.

The generated projection prefix must read the captures from that application
snapshot, including after an exclusive parent has logically been consumed.

## Actual behavior

`fir_cmatch_*` only compares target, arity, and fixed-count metadata.
`fir_cproj_*` only reads the live closure allocation. Neither helper consumes
the parent nor retains captures, so the callee receives borrowed heap values.

## Proof or differential evidence

The same HitScene queries execute through native Lean and the VIR oracle. In
the resident Wasm module, the mapped trap stack is:

```text
Illuminate.StrokeTrace.ofPathData._lam_0._boxed
fir_float_unbox
```

Simple bounds and single-use fill/stroke probes pass. Repeated traversal is the
small distinguishing behavior.

## Semantic impact

Any self-contained Wasm artifact that repeatedly applies a closure with owned
heap captures can fault or observe released storage. The earlier shared
semantic-host repair did not install the corresponding resident helper
protocol.

## Classification and triage

This is a W7 executable-helper omission against an already-landed shared
contract. The generation lane owns the implementation; W6 retains ownership
of its refinement proof.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The resident matcher now delegates every successful match to one shared
`fir_take_closure_application` helper. It validates the static capture
descriptor, consumes exclusive/shared parent ownership, retains shared object
captures through the ordinary resident increment helper, and records a private
single-threaded application snapshot. Projection helpers transfer every
non-erased capture from that snapshot and canonically release an exclusive
parent only after the final generated projection.

The shared helper avoids duplicating descriptor dispatch into every matcher.
Standalone symbolic guards pass, and the real HitScene repeated-stroke path
passes the 301-query oracle plus the 10,000-query flat-frontier regression. W6
still owns the separate implementation-to-concrete-runtime refinement theorem.

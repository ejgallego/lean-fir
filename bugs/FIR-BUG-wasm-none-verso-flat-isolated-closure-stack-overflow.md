---
id: FIR-BUG-wasm-none-verso-flat-isolated-closure-stack-overflow
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-14
reproduction: integration/verso-flat/check-flat.mjs
regression: none
---

# Summary

The honestly regenerated post-cache-isolation Verso Flat closure exhausts the
Wasm call stack on the accepted 2,047-node balanced `Std.Format` input even
though the previous captured closure and the native Lean oracle accept it.

## Minimal reproduction

Compile `VersoSlides.Pretty.formatRenderedForRuntime` from the clean pinned
Verso revision and render the `balanced(10)` document in
`integration/verso-flat/check-flat.mjs`. It contains 1,024 text leaves and
1,023 append nodes. The adapter encodes the input successfully, and seven
smaller differential cases execute before the balanced render traps.

## Exact commands

From the W7 worktree, with a clean checkout of the pinned Verso revision at
`/tmp/fir-w72-verso-flat`, run:

```sh
cd integration/verso-flat
VERSO_ROOT=/tmp/fir-w72-verso-flat bash check.sh
```

## Expected semantics

The Wasm result equals the native Lean result: 1,024 lambda characters with
the same Flat tag events. Input size is bounded by linear memory rather than
the engine call stack. The accepted pre-isolation package and FIR's existing
production `prettyM` stack-shape regression both handle the same balanced
shape.

## Actual behavior

The package publishes deterministically, verifies all checksums, and passes
its basic smoke. The differential check then raises:

```text
RangeError: Maximum call stack size exceeded
    at wasm://wasm/...:wasm-function[683]
    at wasm://wasm/...:wasm-function[688]
    at wasm://wasm/...:wasm-function[702]
    at wasm://wasm/...:wasm-function[44]
    at wasm://wasm/...:wasm-function[45]
    at wasm://wasm/...:wasm-function[20]
```

## Proof or differential evidence

The same generated package passes its small structured smoke, has zero Wasm
imports and zero unresolved runtime operations, and retains the exact 24
reviewed external contracts. Native Lean produces the expected balanced
output. The failure appears only after replacing the stale 90-declaration
capture with the independently reviewed 115-declaration isolated closure.

## Semantic impact

The current generic capture path cannot republish Verso Flat honestly: keeping
the old closure ratchet would conceal compiler-state dependence, while
accepting the new ratchet would reject a valid document already covered by the
package contract. Other closure-heavy `prettyM` clients may share the gap.

## Classification and triage

This is provisionally a W7 code-generation control-flow defect. The repeating
cycle spans several Wasm functions rather than the single direct recursive
worker repaired by the existing self-tail-call rewrite. Minimize and classify
whether the isolated closure exposes mutual tail recursion, tail calls through
generated closure applications, or a newly non-tail call path. It changes no
W6 layout or resident-helper signature.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved

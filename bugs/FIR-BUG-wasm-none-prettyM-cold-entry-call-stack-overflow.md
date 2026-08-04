---
id: FIR-BUG-wasm-none-prettyM-cold-entry-call-stack-overflow
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-04
reproduction: integration/talos/artifact/check-prettyM-browser-adapter.mjs
regression: integration/talos/artifact/check-prettyM-browser-adapter.mjs
---

# Summary

The zero-function-import native `Std.Format.prettyM` artifact can exhaust the
engine's Wasm call stack when a large valid `Std.Format` is the first
substantial entry call in a fresh instance.

## Minimal reproduction

Instantiate the production artifact and, before rendering any smaller input,
render a balanced append tree of depth ten: 1,024 one-character text leaves
and 1,023 append nodes, or 2,047 `Format` nodes in total, at width 80.
Preparation and raw heap encoding succeed. The exported entry traps during
execution.

A grouped document with 256 break opportunities and 1,026 `Format` nodes at
width 16 exhibits the same failure.

## Exact commands

From the W7 worktree, run the packaged browser-adapter smoke test after its
cold-entry regression has been added:

```sh
cd integration/talos/artifact/_build/prettyM-current
node smoke.mjs
```

## Expected semantics

Both documents render to the same styled `PrettyTrace` as Lean 4.32 native,
VIR JSON, VIR direct-`Format`, and LLVM. Valid input size is bounded by the
document and linear-memory limits, not by whether the engine has previously
optimized the entry's callees.

## Actual behavior

Node raises:

```text
RangeError: Maximum call stack size exceeded
    at wasm://wasm/...:wasm-function[3]:0x2e99
    at wasm://wasm/...:wasm-function[3]:0x44bc
    ...
```

Function index 3 is the compiler-generated recursive
`Std.Format.be._at_.Std.Format.prettyM...` worker. Its tail-recursive work-list
steps are emitted as ordinary self-calls. A successful smaller render may
cause engine tier-up and reduce the physical frame size enough to mask the
failure, making the behavior dependent on call history.

## Proof or differential evidence

The balanced and grouped inputs pass through the JavaScript, VIR JSON, VIR
direct-`Format`, and LLVM paths. The browser adapter reports that preparation
completed and encoded all 2,047 nodes before the Wasm entry call fails.

## Semantic impact

The packaged artifact rejects valid documents nondeterministically with
respect to engine optimization state. This affects the raw entry as well as
the browser adapter and cannot be repaired by frontier synchronization or a
different JavaScript heap encoder.

## Classification and triage

This is a W7 code-generation control-flow defect. It does not require a W6
concrete-layout or resident-helper signature change. The existing symbolic
Wasm loop and branch surface can express direct self-tail recursion without a
native Wasm call.

## Workaround

Rendering a smaller document first may mask the failure on some engines, but
is not a valid correctness or portability workaround.

## Upstream tracking

none

## Resolution and regression

W7 now runs a validated post-lowering pass over the closed resident module.
Every direct self-call in Wasm tail position is replaced by reverse-order
parameter assignment and a branch to a structured function-body loop. The
rewrite uses only the existing standard Wasm loop/branch surface and changes
neither final LCNF nor the runtime ABI.

The packaged browser-adapter check makes the 2,047-node balanced append tree
the first entry call in a fresh process. The fixed artifact also passes the
reported 1,026-node grouped document as the first call and a cold 32,767-node
balanced tree. Existing styled, arbitrary-precision numeric, 1 MiB UTF-8,
frontier-synchronization, and repeated-call checks continue to pass.

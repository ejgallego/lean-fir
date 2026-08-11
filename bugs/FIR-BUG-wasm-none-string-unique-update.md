---
id: FIR-BUG-wasm-none-string-unique-update
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: resident-runtime-test
first-seen: 2026-08-12
reproduction: integration/talos/artifact/run-resident-string.mjs
regression: integration/talos/artifact/resident-string-client.mjs
---

# Summary

The resident String append and push helpers allocate a fresh exact-length
object on every call and do not consume their owned String input. This loses
Lean's exclusive-update and geometric-capacity behavior and leaks every
intermediate live String in the instance arena.

## Minimal reproduction

Create an ordinary live String, record the resident heap frontier, and call
`String.Internal.pushn source '!' 0`. Lean's generic definition returns the
owned source directly. The resident helper instead allocates and copies a new
String, changing both the address and frontier.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-string _build/resident-string.wasm
node run-resident-string.mjs _build/resident-string.wasm
```

## Expected semantics

`String.Internal.pushn` repeatedly uses the generic `String.push` path. Zero
repetitions return the owned source without allocation. Nonzero push and
append calls reuse an exclusive String when capacity permits; otherwise they
grow it, transferring the source allocation when exclusive or consuming one
reference when shared.

## Actual behavior

`pushn` and append always call the exact-size resident allocator and copy the
source payload. The source header remains live at reference count one.

## Proof or differential evidence

The real-engine resident String fixture checks zero-count address identity and
frontier stability. Before repair it reports that `pushn` returned a different
address.

## Semantic impact

String contents are correct, but builders such as `Std.Format.prettyM` become
quadratic and retain dead intermediate strings. This defeats the ownership
semantics on which Lean's generated code relies for practical execution.

## Classification and triage

This is a resident-runtime compiler defect. Final LCNF calls the ordinary
String API; FIR's helper introduces the divergent allocation behavior.

## Workaround

None. Replacing the builder with a JavaScript or application-specific helper
would bypass the compiled Lean semantics.

## Upstream tracking

none

## Resolution and regression

The resident String helper now derives usable capacity from the retained
allocation extent while preserving the frozen header shape: `aux1` remains
the logical UTF-8 byte length and `aux2`/`aux3` remain zero. Zero-count
`pushn` returns its owned source directly. Append and nonzero push reuse an
exclusive source when the result fits, otherwise allocate geometric spare
capacity and consume the old source through the generic release helper.
Shared and persistent sources always take copy-on-write paths; the borrowed
right append operand is never consumed.

The real-engine fixture covers zero-count identity/frontier stability,
exclusive in-place append, exclusive growth and old-header retirement,
reuse after growth, shared reference consumption, persistent copy-on-write,
borrowed-right ownership, and repeated pushes with a flat frontier inside
retained capacity.

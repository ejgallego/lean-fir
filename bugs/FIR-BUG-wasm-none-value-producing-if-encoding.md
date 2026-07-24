---
id: FIR-BUG-wasm-none-value-producing-if-encoding
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-24
reproduction: Fir/Wasm/Examples.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

The symbolic validator accepts a value-producing `ifElse`, but the binary
encoder always emits its WebAssembly `if` with the empty block type.

## Minimal reproduction

A result-free symbolic function pushes an `i32` condition, then executes an
`ifElse` whose reachable arm leaves one `UInt32` on the operand stack and
whose other arm is `unreachable`. `validateModule` accepts that function.

## Exact commands

From the repository root:

```sh
lake build Fir.Wasm.Examples
node integration/talos/artifact/run-resident-read-projections.mjs \
  integration/talos/artifact/_build/resident-read-projections.wasm
```

The symbolic projection module validates and encodes, but V8 rejects the
binary with `expected 0 elements on the stack for fallthru, found 1`.

## Expected semantics

Every module accepted by the symbolic validator and successfully encoded
should pass standard WebAssembly validation. Because the current encoder emits
`0x40` as every `if` block type, reachable arms must restore the operand stack
present after consuming the condition.

## Actual behavior

`Validate.checkInstruction` merges the reachable arm stack and permits it to
differ from the post-condition input stack. `Emit.Binary.encodeInstruction`
does not encode a corresponding result block type, producing an invalid
binary.

## Proof or differential evidence

The standalone eight-helper resident projection module passes
`Fir.Wasm.validateModule` and `Fir.Wasm.Emit.encode`; `WebAssembly.validate`
returns false for the emitted 935-byte artifact, and V8 identifies function
zero's extra fallthrough stack element.

## Semantic impact

An apparently validated FIR Wasm module can be rejected by all standard
engines. Any helper that returns a loaded value directly through a checked
conditional path is affected.

## Classification and triage

This is local to the symbolic Wasm validator/encoder agreement. It does not
change LCNF semantics or the W6 linear-memory layout.

## Workaround

Store conditional results in typed locals so every encoded `if` remains
stack-neutral, then load the local before returning.

## Upstream tracking

none

## Resolution and regression

The symbolic validator now requires every reachable `ifElse` fallthrough to
restore the operand stack present after consuming its condition, matching the
encoder's explicit empty block type. `Fir/Wasm/Examples.lean` permanently
rejects the former value-producing shape. Resident projection helpers store
their loaded result in a typed local inside the conditional guard and load it
only after the stack-neutral `if` has completed.

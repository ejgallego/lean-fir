---
id: FIR-BUG-wasm-none-js-float-signaling-nan-transport
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-30
reproduction: integration/talos/artifact/test-concrete-floats.mjs
regression: integration/talos/artifact/test-concrete-floats.mjs
---

# Summary

Transporting raw signaling-NaN arguments through JavaScript `number` and a
Wasm `f32` or `f64` export quiets the NaN before the compiler-produced function
observes it.

## Minimal reproduction

Instantiate the generated `source-float32-id.wasm` or
`source-float64-id.wasm` identity module, convert signaling-NaN bits to a
JavaScript `number`, call the exported floating identity, and convert the
result back to bits.

## Exact commands

Run `node integration/talos/artifact/test-concrete-floats.mjs` after adding
engine identity assertions for `0x7fa12345` and `0x7ff123456789abcd`.

On V8, direct `number`-lane calls currently produce `0x7fe12345` and
`0x7ff923456789abcd`.

## Expected semantics

The bit-exact source invocation boundary must preserve every raw IEEE-754 bit,
including the quiet/signaling discriminator and payload, without JavaScript
numeric coercion.

## Actual behavior

Quiet NaNs preserve their payloads, but signaling NaNs are quieted while
crossing the JavaScript-to-Wasm floating lane. The generated Wasm identity
itself does not perform arithmetic.

## Proof or differential evidence

`0x7f800001` becomes `0x7fc00001`, `0x7fa12345` becomes `0x7fe12345`,
`0x7ff0000000000001` becomes `0x7ff8000000000001`, and
`0x7ff123456789abcd` becomes `0x7ff923456789abcd`. Quiet-NaN controls retain
their exact bits.

## Semantic impact

The JSON manifest remains exact, but JavaScript clients cannot claim
bit-exact execution for every Float32/Float input through the raw floating
export. Signaling-NaN identity, boxing, packed-field, and closure-capture
tests would otherwise observe changed bits.

## Classification and triage

This is a Wasm adapter boundary issue. The safe boundary must carry raw bits as
`i32`/`i64` and reinterpret them inside Wasm, while retaining the original
compiler ABI export for low-level consumers.

## Workaround

Use a generated integer-lane wrapper that reinterprets its parameter to
`f32`/`f64`, invokes the compiler entry, and reinterprets the result back to
`i32`/`i64`.

## Upstream tracking

none

## Resolution and regression

The source compiler now exports a canonical integer-lane facade for every
entry with a Float32 or Float parameter/result and records it in the
version-1 `bitExactFloatTransport` manifest capability. Shared consumers
validate that capability, pass Float32/Float bits through `i32`/`i64`, and
reinterpret only inside Wasm.

`test-concrete-floats.mjs` executes positive and negative signaling NaNs,
quiet NaNs, signed zeros, infinities, and maximal payloads through the generated
facades. The canonical invocation probes use `0x7fa12345` and
`0x7ff123456789abcd`; the Node module client and Chrome concrete-corpus Worker
both preserve those exact payloads. Missing, malformed, unknown, and
schema-mismatched capabilities fail closed.

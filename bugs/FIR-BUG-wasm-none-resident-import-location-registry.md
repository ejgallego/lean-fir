---
id: FIR-BUG-wasm-none-resident-import-location-registry
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-27
reproduction: integration/talos/artifact/call-concrete-pretty-format.mjs
regression: none
---

# Summary

A remaining JavaScript import cannot decode a valid Wasm-resident string
argument because the address has no JavaScript allocator location.

## Minimal reproduction

Compile text `Std.Format.prettyM` after internalizing its supported
`stringLiteral` operations while retaining its string-processing externals.
The resident helper allocates a valid W6 UTF-8 string and passes its raw object
word to the next imported handler.

## Exact commands

From the repository root after generating the source artifacts:

```sh
node integration/talos/artifact/call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-literals.wasm
```

## Expected semantics

The imported handler should observe the same live string that the FIR runtime
allocated for the literal. Resident and host operations already share module
memory and one monotone frontier.

## Actual behavior

`ConcreteHost.external` decodes the object argument through
`ConcreteHost.decode`, which calls `locationOf`. Only allocations made or
loaded by the JavaScript host populate `addressLocations`; the resident string
address therefore fails with `concrete address ... has no logical location`.

## Proof or differential evidence

The standalone zero-import literal module validates and its Node client checks
the exact header, UTF-8 bytes, padding, and direct `ConcreteHost.readString`
result. The linked module also validates and removes the expected imports, but
the native-oracle concrete call fails at the first remaining external that
receives the Wasm-born string.

## Semantic impact

String literals cannot be moved behind the resident boundary before their
JavaScript-consuming external family. Guessing logical locations or
constructor descriptors from raw memory would risk changing allocation
identity or ownership behavior. The final zero-function-import artifact is not
blocked because no JavaScript decoder participates there.

## Classification and triage

This is provisionally a `wasm-adapter` limitation in the temporary mixed
runtime. The resident string bytes satisfy the current W6 layout; the failure
is solely in host-only allocation bookkeeping.

## Workaround

Internalize immediate Natural literals independently. Keep `stringLiteral`
imports until every reachable string consumer is resident, then link the
already-tested resident UTF-8 helper without crossing the JavaScript boundary.

## Upstream tracking

none

## Resolution and regression

unresolved

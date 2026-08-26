# Scalar boxing conformance audit

Audit date: 2026-08-26.  Reference toolchain: Lean 4.33.0 at
`d8b18978322de05a8f3dba51ef03cf5461676c17`.  FIR target contract:
`wasm32-lean64`.

## Scope

Lean's final impure LCNF has exactly seven scalar types that may reach the
`box` and `unbox` instructions:

- `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize`;
- `Float32` and `Float`.

This list comes from `Lean.Expr.isScalar` in upstream
`Lean/Compiler/LCNF/Types.lean`.  Signed fixed-width source types, `ISize`,
`Bool`, `Char`, and scalar enums do not add distinct final-LCNF box families:
they lower through one of these scalar lanes or through an object/tagged
representation.

`ExplicitBoxing` may introduce a box at any scalar-to-object boundary.  Its
generated `_boxed` adapters use the exact result of `Lean.Expr.boxed`, while a
generic polymorphic cast may request the wider `tobject` result.  A complete
backend must therefore cover both the representation policy and every
compiler-emitted result-kind spelling.

## Upstream policy and FIR status

| Scalar | Exact `_boxed` result | Upstream operation on the captured Lean64 host | FIR semantic / W6 policy | W7 resident generation | Status |
|---|---|---|---|---|---|
| `UInt8` | `tagged` | generic `lean_box` / `lean_unbox`; always tagged | tagged | box/unbox, zero-import | conformant |
| `UInt16` | `tagged` | generic `lean_box` / `lean_unbox`; always tagged | tagged | generic `tobject` and exact `tagged` boxes share one physical-body factory; both close with zero imports | generation conformant; alias proof pending |
| `UInt32` | `tobject` | `lean_box_uint32`; tagged on Lean64 | semantic tag; direct wasm32 immediate or persistent promoted tag | box/unbox, zero-import | conformant for the named `wasm32-lean64` contract |
| `UInt64` | `object` | `lean_box_uint64`; always ordinary heap | ordinary heap box | generic `tobject` and exact `object` boxes share one physical-body factory; both close with zero imports | generation conformant; generic helper contract-proved, alias proof pending |
| `USize` | `tobject` | `lean_box_usize`; always ordinary heap | current main still uses the payload/tag split | no box/unbox helper | confirmed shared semantic gap plus W7 gap |
| `Float32` | `object` | `lean_box_float32`; always ordinary heap | semantic box is heap-only; no stable W6 resident-box descriptor/refinement | no box/unbox helper | confirmed W7/W6 coverage gap |
| `Float` | `object` | `lean_box_float`; always ordinary heap | semantic box is heap-only; resident proof remains separate | box/unbox, zero-import | generation-ready; W6 theorem remains separate |

The upstream C emitter selects the generic `lean_box` path only for `UInt8`
and `UInt16`.  It selects the five type-specific APIs for the other families.
`lean_box_uint64`, `lean_box_usize`, `lean_box_float32`, and `lean_box_float`
allocate unconditionally.  `lean_box_uint32` is target-dependent: it tags on a
64-bit host and allocates on a 32-bit host.

FIR deliberately transports captured Lean64 semantics over wasm32 addresses.
Consequently, high `UInt32` tags use a persistent promoted-natural object in
linear memory.  This is a representation bridge covered by the refinement
witness, not a claim that FIR matches upstream's native wasm32 C layout.  The
separate `FIR-BUG-wasm-none-usize-target-width-contract` card records that
target-model boundary.

## Executable probe

A diagnostic source probe used a no-inline polymorphic identity to force one
generic box/unbox pair for each family, then applied the ordinary closed
resident linker with `requireNoRuntimeOperations := true`.

| Entry payload | Base box result | Runtime operations after resident link |
|---|---|---|
| `UInt8` | `tagged` | 0 |
| `UInt16` | `tobject` | 0 |
| `UInt32` | `tobject` | 0 |
| `UInt64` | `tobject` | 0 |
| `USize` | `tobject` | 2: box and unbox |
| `Float32` | `object` | 2: box and unbox |
| `Float` | `object` | 0 |

A second probe passed a monomorphic scalar identity as a first-class function,
forcing Lean's generated `_boxed` declaration.  `UInt8`, `UInt32`, `USize`,
`Float32`, and `Float` reached lowering with the upstream result kinds shown
above.  FIR rejected these two valid declarations:

```text
def rawUInt16._boxed value : tagged :=
  let value.boxed := unbox value
  let res := rawUInt16 value.boxed
  let r := box res
  return r

def rawUInt64._boxed value : obj :=
  let value.boxed := unbox value
  dec[ref] value
  let res := rawUInt64 value.boxed
  let r := box res
  return r
```

The accepted repair derives the exact annotation from upstream
`Lean.Expr.boxed`, while `boxResultKind type declared` preserves FIR's existing
generic `tobject` refinement.  The checker now recognizes exact
`UInt16 -> tagged` and `UInt64 -> object` results and still rejects the
converse malformed annotations.  Resident linking maps each exact operation
to a signature-specific alias generated from the same physical helper-body
factory as its generic operation.

The probe is now permanent in
`Fir/Wasm/Emit/ScalarBoxingExamples.lean`. It compiles fourteen real Lean
entries: one generic polymorphic round trip and one compiler-generated
`_boxed` closure wrapper for each family. Exact wrapper result kinds are read
from `upstreamBoxResultKind?`, not repeated in the fixture. The five ready
families must link with zero imports and zero runtime operations. `USize` and
`Float32` are not skipped: each must retain exactly its matching box/unbox
pair, so any accidental widening or unrelated residual operation fails the
fixture. Their readiness flags become zero-frontier ratchets when the shared
contract and resident helpers land.

## Findings and order

1. Finish the already isolated heap-only `USize` contract stack, then add W7
   resident box/unbox and a zero-import executable round trip.  This is the
   only observed representation-semantic discrepancy.
2. **Generation complete.** Exact `_boxed` result-kind admission for `UInt16`
   and `UInt64` uses upstream's mapping; physical-signature-compatible
   resident aliases share the generic helper-body factories.  W6 may later
   connect those aliases to the already proved physical helper contracts.
3. Add heap-only, bit-exact `Float32` resident box/unbox support.  Promote its
   layout marker through W6 rather than inventing a W7-private proof contract.
4. Ratchet all seven generic paths and all seven generated `_boxed` paths in a
   source-generated external-engine fixture.  Require zero imports and zero
   runtime operations after linking.
5. Keep native wasm32 target semantics as a separate target-contract decision;
   do not silently reinterpret the current `wasm32-lean64` artifacts.

## Bug-card inventory

- `FIR-BUG-impure-none-uint64-box-tagged`: fixed representation mismatch.
- `FIR-BUG-impure-none-usize-box-tagged`: confirmed; isolated contract stack
  is awaiting dependent W6/W7 completion.
- `FIR-BUG-wasm-none-boxed-scalar-result-kind-drift`: confirmed admission and
  resident-alias gap for exact `UInt16`/`UInt64` adapters.
- `FIR-BUG-wasm-none-float32-resident-boxing`: confirmed resident/proof
  coverage gap.
- `FIR-BUG-wasm-none-usize-target-width-contract`: confirmed, intentionally
  separate target-model issue.

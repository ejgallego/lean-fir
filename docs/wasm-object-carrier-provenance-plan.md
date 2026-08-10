# Wasm object carrier and provenance plan

## Problem

Final LCNF has three related object annotations:

- `object`: a heap object;
- `tagged`: an immediate tagged value; and
- `tobject`: either representation.

All three cross an upstream Lean C call boundary as `lean_object *` and occupy
one Wasm `i32` lane. They are therefore physically interchangeable at an
ordinary compiler-produced call, return, or join assignment. They are not
semantically interchangeable: projection, mutation, deletion, and some
ownership operations require evidence that the value is a heap object, while
constructor-tag operations must remain valid for both tagged and heap values.

FIR currently records both facts in `AbiKind`. `AbiKind.refines` is the
directional semantic relation, while `AbiKind.leanCompatible` adds symmetric
object-family compatibility for ordinary transfers. This division fixed real
compiler-generated joins and calls. The HitScene repair then added
`effectiveDeclarationResultKind?`, a conservative straight-line analysis that
retains an exact heap or tagged result through named calls and lazy caches.

The accepted implementation is sound for its supported fragment and has W6
coverage, but the abstraction is overloaded: a single `AbiKind` is asked to
describe a physical carrier, an LCNF annotation, and locally proved semantic
provenance. This makes every new boundary choose between overly strict
refinement and overly broad physical compatibility.

## Proposed model

Keep the source annotation, carrier, and provenance as separate axes.

```text
Source annotation     Carrier              Provenance
-----------------     ----------------     -------------------
object                objectWord / i32     heap
tagged                objectWord / i32     tagged
tobject               objectWord / i32     heap-or-tagged
erased                erasedWord / i32     erased
reuseToken            reuseWord / i32      reuse capability
integer scalars       scalar lane          exact scalar kind
floats                float lane           exact float kind
```

The names above describe the design, not a committed public API. The first
implementation should use the smallest Lean data types that make the following
judgments explicit:

1. `carrierCompatible actual expected`: a symmetric physical transfer check;
2. `provenanceRefines actual expected`: the existing directional semantic
   check; and
3. `operationAccepts requirement evidence`: a check that a heap-sensitive
   operation has sufficient provenance.

Scalar kinds remain exact even when two of them share `i32`; physical equality
of Wasm value types alone is never enough. Likewise, object-word carrier
compatibility must not authorize a heap dereference.

## Evidence flow

The compiler should carry a small value descriptor rather than replacing an
LCNF annotation with an inferred `AbiKind`:

```text
ValueInfo := source annotation + physical carrier + proved provenance
```

Evidence originates from syntax whose representation is fixed by final LCNF:

- constructors with fields produce heap evidence;
- nullary constructors produce tagged evidence;
- boxing uses Lean 4.32's representation rule for the scalar type;
- literals retain their established literal invariant;
- a named call uses the callee's proved result evidence;
- an `isShared(value) == false` path may refine that exact value to heap;
- branches and joins combine evidence conservatively.

`effectiveDeclarationResultKind?` remains the accepted implementation while
this model is introduced. Its straight-line recognizer becomes the first
producer of result evidence, not the long-term definition of a declaration's
ABI.

## Boundary rules

- Calls, returns, joins, and partial-application capture require compatible
  carriers and source-level arity/type agreement.
- Exact provenance propagates across those boundaries when it is proved; an
  unknown `tobject` remains unknown.
- Closure metadata records the carrier needed to store and reload captures and
  the provenance known for each capture. It must not infer heap provenance from
  an `i32` field.
- Lazy caches store the physical carrier selected by the target and retain the
  same result evidence on cache-hit and cache-miss paths.
- Projection, mutation, reuse, and deletion state their semantic requirements
  explicitly. Their admission cannot be justified by carrier compatibility.
- Runtime helper signatures continue to describe semantic operands. A later
  lowering step maps those operands to Wasm value types.

## Vertical slices

1. **Freeze behavior.** Add table-driven examples for all nine combinations of
   `object`, `tagged`, and `tobject` at ordinary transfers, plus negative heap
   operations on unknown/tagged values. Keep the HitScene boxed-Float partial
   capture and tagged-Nat cache cases as end-to-end regressions.
2. **Introduce descriptors.** Add carrier and provenance definitions alongside
   `AbiKind`, with executable correspondence checks and elementary theorems.
   Do not change compiler output in this slice.
3. **Thread evidence.** Replace `LocalKinds` internally with value descriptors
   at call, return, join, partial-capture, and closure-dispatch boundaries.
   Preserve the emitted symbolic Wasm and artifact digests where behavior is
   unchanged.
4. **Move operation gates.** Make heap-sensitive operations consume provenance
   requirements instead of testing ad hoc `AbiKind` combinations.
5. **Adapt W6.** After the shared descriptor/signature commit lands, prove that
   carrier erasure agrees with concrete layout and that validated provenance is
   sound for cache, closure, projection, ownership, and reuse paths.
6. **Retire the compromise.** Express declaration result recovery as evidence,
   remove redundant `leanCompatible`/`refines` choices, and rerun HitScene,
   Flat, PrettyFormat, root, Talos, and deterministic artifact gates.

## Acceptance and non-goals

The replacement is accepted only when:

- no consumer treats `tobject` as heap without explicit evidence;
- compiler-generated object-family transfers match upstream Lean's generic C
  path;
- exact heap/tagged evidence survives named calls, closure captures, closure
  dispatch, and lazy caching;
- malformed scalar/object crossings remain rejected; and
- existing Wasm artifacts and external-engine differentials remain green.

This milestone does not change Lean's LCNF, invent a second object encoding,
or add a client-visible ABI. It is an internal compiler/proof refactor intended
to make the current behavior compositional.

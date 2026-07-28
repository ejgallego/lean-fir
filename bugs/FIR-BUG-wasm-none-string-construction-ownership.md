---
id: FIR-BUG-wasm-none-string-construction-ownership
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-28
reproduction: scripts/wasm_format_externals.mjs
regression: Fir/Validation/Corpus.lean
---

# Summary

The V8 handlers for `String.Internal.append` and `String.Internal.pushn`
always allocate and never consume their owned String argument, unlike Lean's
native copy-on-write ownership semantics.

## Minimal reproduction

Invoke the current `String.Internal.append` handler with an exclusive source
cell. It leaves that cell unchanged and allocates a second cell. With source
reference count two, it allocates the result but leaves the source count at
two. Invoking `String.Internal.pushn` with count zero also allocates a second
identical String.

## Exact commands

Run a Node probe using `SemanticHost` and `formatExternalRegistry`:

```sh
node --input-type=module -e \
  'import { SemanticHost } from "./scripts/wasm_semantic_host.mjs";
   import { formatExternalRegistry as r } from "./scripts/wasm_format_externals.mjs";
   const h = new SemanticHost();
   const s = h.alloc({kind:"string", value:"A"});
   const v = r["String.Internal.pushn"]({
     args:[s,{kind:"scalar",scalarKind:"uint32",value:0x1f600n},h.natural(0n)],
     host:h,world:h.world}).value;
   console.log(s.location, v.location, h.liveCell(s.location));'
```

Compile a C probe with `lake env leanc` that calls `lean_string_append` and
`lean_string_pushn` directly, using `lean_inc` to construct the shared source
case and `lean_is_exclusive` to inspect the post-call references.

## Expected semantics

Lean's native runtime mutates or logically reuses a consumed exclusive String.
For a shared consumed source it allocates a result and decrements the source
ownership count. `pushn` with count zero returns the source unchanged. Borrowed
append operands remain unchanged in every path.

## Actual behavior

Both JavaScript handlers decode the inputs, allocate an unconditional String
result, and leave every source cell and reference count untouched.

## Proof or differential evidence

A direct Lean runtime probe reports an exclusive append result, decrements a
shared append source from count two to one, returns the same source for
zero-count `pushn`, and returns distinct exclusive source/result objects after
positive-count shared `pushn`. The current semantic host allocates in the
unique and zero-count cases and retains source count two in the shared case.

## Semantic impact

Pure String results remain extensionally equal, but subsequent `isShared`,
mutation, reset/reuse, allocation, and heap-identity behavior can diverge.
This prevents the V8 engine from serving as an exact ownership oracle for
compiler-generated String construction.

## Classification and triage

Lean's runtime implementation and direct runtime probe agree. The mismatch is
in the JavaScript external implementation, so it is classified as a Wasm
adapter defect. The Talos concrete formatting registry duplicates these
handlers and must consume the same shared contract without lane-4 editing its
track-owned files.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Fixed in `ec8efe1` by sharing exact copy-on-write handlers between the
validation and formatting registries and pinning every ownership path with
Lean and JavaScript guards. Nine `string-append-*` and `string-pushn-*` corpus
cases compare Lean native execution, LCNF, and V8 across unique, shared,
self-aliased, empty, zero-count, and non-BMP construction boundaries.

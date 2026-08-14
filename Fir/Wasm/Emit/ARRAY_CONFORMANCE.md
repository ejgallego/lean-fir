# Resident Array conformance

This note pins W7's resident Array lowering to the upstream Lean runtime used
to compile the source closure. It distinguishes Lean execution from FIR's
foreign linear-memory boundary.

## Version and sources

The current FIR toolchain is Lean `v4.33.0`, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`. The audited definitions are:

- `src/include/lean/lean.h`: `lean_array_fget`, `lean_array_uget`,
  `lean_array_fset`, `lean_array_uset`, `lean_array_fswap`,
  `lean_array_uswap`, `lean_array_get`, `lean_array_set`, `lean_array_pop`, and
  the Array layout/accessors;
- `src/runtime/object.cpp`: Array copy/expand and panic implementations; and
- `src/lean/Init/Data/Array/{Basic,Set}.lean`: proof-indexed versus dynamically
  checked source APIs and their extern mappings.

The same relevant implementation was inspected in Lean `v4.32.0`. Conformance
is nevertheless versioned: a future runtime signature or ownership change must
update this note and the package metadata rather than silently inherit this
classification.

## Operation matrix

| Lean declaration | Index contract | Upstream hot path | Ownership/result |
| --- | --- | --- | --- |
| `Array.getInternalBorrowed` | erased `i < size` proof | direct immediate-Nat unbox and slot load | borrowed element |
| `Array.getInternal` | erased `i < size` proof | direct immediate-Nat unbox and slot load | incremented element |
| `Array.ugetBorrowed` | erased `i < size` proof | direct `USize` slot load | borrowed element |
| `Array.uget` | erased `i < size` proof | direct `USize` slot load | incremented element |
| `Array.set` | erased `i < size` proof | direct Nat unbox, ensure exclusive, replace | consumes Array and value; releases old element |
| `Array.uset` | erased `i < size` proof | direct `USize`, ensure exclusive, replace | consumes Array and value; releases old element |
| `Array.swap` | two erased bounds proofs | direct Nat unboxes, ensure exclusive, swap | consumes Array |
| `Array.get!Internal{Borrowed,}` | dynamic Nat | scalar and bounds branch; otherwise panic/default | borrowed or incremented in-bounds element; incremented fallback |
| `Array.set!` | dynamic Nat | scalar and bounds branch; otherwise panic/original | consumes value; consumes/returns Array according to upstream path |
| `Array.pop` | none | ensure exclusive; empty is unchanged; otherwise shrink and release last | consumes Array |
| `Array.push` | none | unique spare-capacity mutation or upstream copy/growth policy | consumes Array and value |
| `Array.size` / `Array.usize` | none | direct cached-size load | boxed Nat / machine `USize` |

`swapIfInBounds` follows the dynamic family when it enters the resident
frontier: it checks both indices and returns the original Array unchanged on
failure.

## FIR rule

Typed closed applications use two independent policies:

1. the resident representation invariant removes repeated Array-header
   validation; and
2. an erased source proof removes index validation and bounds branches only for
   the proof-indexed rows above.

The Nat proof rows use Lean's `lean_unbox` shape. On wasm32, any live Array that
fits memory has fewer elements than the maximum immediate Nat payload, so an
index proven smaller than its size is a canonical immediate. The W6 refinement
must discharge this representation fact together with the erased bounds
premise.

Standalone/public resident helpers retain structural and bounds validation for
foreign callers. Malformed foreign memory has no Lean Array semantics. Dynamic
Lean APIs retain their source-defined failure behavior even in a trusted
closed application.

Binary compatibility with Lean's native C `lean_array_object` is not claimed.
FIR instead requires observational agreement for related well-typed states:
values, mutation visibility, uniqueness/copy-on-write, ownership, panic
behavior, and traps.

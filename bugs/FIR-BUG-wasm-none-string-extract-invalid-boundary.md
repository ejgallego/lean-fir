---
id: FIR-BUG-wasm-none-string-extract-invalid-boundary
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-28
reproduction: scripts/wasm_format_external_algorithms.mjs
regression: none
---

# Summary

The V8 String extraction helper slices arbitrary UTF-8 byte ranges, while native
Lean requires the start to be an exact scalar boundary and handles an invalid
end position by continuing to the String end.

## Minimal reproduction

Use source `"Aé😀Z"`, whose UTF-8 byte positions are `0, 1, 3, 7, 8`.
Native `String.Internal.extract source ⟨4⟩ ⟨7⟩` returns `""`, but
`stringExtract(source, 4n, 7n)` returns `"���"`. Native extraction from
positions `3` to `4` returns `"😀Z"`, while the helper returns `"�"`.

## Exact commands

Run the current helper from the repository root:

```sh
node --input-type=module -e \
  'import { stringExtract } from "./scripts/wasm_format_external_algorithms.mjs";
   console.log(JSON.stringify(stringExtract("Aé😀Z", 4n, 7n)));
   console.log(JSON.stringify(stringExtract("Aé😀Z", 3n, 4n)));'
```

Compile and run a Lean program that prints:

```lean
(String.Internal.extract "Aé😀Z" ⟨4⟩ ⟨7⟩).quote
(String.Internal.extract "Aé😀Z" ⟨3⟩ ⟨4⟩).quote
```

with `lake env lean -c`, `lake env leanc`, and the resulting native executable.

## Expected semantics

Native Lean implements extraction by traversing decoded scalar boundaries.
Failure to encounter the exact begin position returns the empty String. Once
the begin position is found, failure to encounter the exact end position
returns the complete remaining suffix.

## Actual behavior

The helper applies `TextDecoder` directly to the selected byte slice.
`TextDecoder` replaces truncated or leading continuation bytes with replacement
characters, producing Strings that native Lean never returns for these inputs.

## Proof or differential evidence

A native-compiled Lean probe and direct Node execution disagree on all three
invalid-start cases tested (`2..7`, `4..7`) and on the invalid-end case `3..4`.
Valid boundaries, reversed ranges, and past-end ranges agree.

## Semantic impact

Any real-Wasm validation fixture or formatting program that calls
`String.Internal.extract` with a raw position inside a multibyte scalar can
produce a V8 observation different from the Lean native source oracle.

## Classification and triage

The compiler and Lean runtime agree with the exposed Lean definition. The
discrepancy is local to the JavaScript semantic-host algorithm, so it is
classified as a Wasm adapter defect.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved

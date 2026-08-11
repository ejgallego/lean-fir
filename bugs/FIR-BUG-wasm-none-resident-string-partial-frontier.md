---
id: FIR-BUG-wasm-none-resident-string-partial-frontier
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-11
reproduction: integration/verso-html/Emit.lean
regression: integration/talos/artifact/resident-string-client.mjs
---

# Summary

The closed-application resident linker rejects a valid partial String external
frontier because `ResidentString.internalizeAvailable` requires every helper in
the historical prettyM String family as soon as any one helper is imported.

## Minimal reproduction

Compile `VersoSlides.Pretty.formatHtmlForRuntime` from Verso commit
`2ee1c804106b87ab254923fc75a0172f382fcd8e`. The source closure imports the
String operations actually used by the specialized HTML renderer, including
`String.Internal.append`, but it does not import the unrelated
`String.Internal.offsetOfPos` declaration.

## Exact commands

```sh
cd integration/verso-html
lake --keep-toolchain --reconfigure \
  -KversoRoot=/tmp/verso-html-2ee1c804 build VersoFirHtml.Compile
lake --keep-toolchain -KversoRoot=/tmp/verso-html-2ee1c804 env lean Emit.lean
```

## Expected semantics

`closedApplicationPolicy` should internalize exactly the supported String
operations present in the captured source closure, after checking each imported
signature. Unrelated String APIs should not be required or linked.

## Actual behavior

`ResidentString.internalizeAvailable` delegates to the strict historical
`internalize` operation whenever any recognized String import is present. The
strict operation then fails with:

```text
missingExternal `String.Internal.offsetOfPos
```

## Proof or differential evidence

The source closure and base Wasm module compile successfully. Resident linking
fails before Wasm execution solely because an unrelated import is absent.

## Semantic impact

Closed applications cannot use a proper subset of the supported resident
String API. They either have to manufacture unused imports or retain host
fallbacks, both of which violate deterministic zero-import package closure.

## Classification and triage

This is a generic resident-linker selection defect, not a Verso interface
problem. Array, numeric, and Float resident families already provide
signature-checked available-operation linking.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentString.internalizeAvailable` now selects exactly the supported String
imports present in the source module, verifies each signature, installs only
their implementation dependencies, and recomputes the residual runtime
frontier. The historical strict `internalize` API and declaration inventory
remain unchanged for existing consumers.

The resident String client covers both the historical internal operations and
the newly admitted public `String.append`, `String.push`, `String.Pos.next`,
and `String.decodeChar` paths, including ASCII, two-byte and four-byte UTF-8
decoding and a past-end trap. The Verso HTML closure is the partial-frontier
integration regression: it links with zero imports without manufacturing any
unrelated String declaration.

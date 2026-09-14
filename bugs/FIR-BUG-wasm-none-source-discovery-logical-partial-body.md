---
id: FIR-BUG-wasm-none-source-discovery-logical-partial-body
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/Provenance.lean
regression: integration/vbp-native-session-probe/PartialBody.lean
---

# Summary

Runtime source discovery reads the logical body of imported partial definitions
instead of the executable body selected by Lean's compiler.

## Minimal reproduction

Run the real renderer pre-final capture and inspect source dependency discovery.
The ListItem.toJson specialization has exact source provenance, but its caller
is absent from the discovered runtime source closure. Its parent Block.toJson
has a logical default-value body; only the executable unsafe-rec body mentions
ListItem.toJson.

## Exact commands

With the pinned fixture and cache/TMPDIR prepared as in REPAIR_RESULT.md:

```sh
cd integration/vbp-native-session-probe
FIR_RENDERER_PROVENANCE=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Provenance.lean
lake --keep-toolchain -KpostponeCompile=false env lean PartialBody.lean
```

## Expected semantics

Source discovery follows the executable body Lean uses in LCNF.toDecl.
Lean.Compiler.LCNF.getDeclInfo? selects the unsafe recursive definition first.

## Actual behavior

sourceRuntimeValueClosure uses Environment.find? and reads the logical body.
The actual renderer closure contains 695 source names and omits ListItem.toJson.
A read-only comparison changing only body selection finds 944 names and the
missing caller. The generated helper itself is not a kernel constant; it is
indexed as an extra declaration in Verso.Doc with native IR and a signature.

## Proof or differential evidence

The structural specializer provenance resolver already returns the exact
ListItem.toJson caller and Array.mapMUnsafe.map callee. Those identities and
their source bodies survive pre-final capture unchanged. This isolates the
missing edge to source discovery, not a name-prefix interpretation or reset.

## Semantic impact

Capture rejects a compilable renderer before Wasm generation. No incorrect
generated execution has been established.

## Classification and triage

W7 source-discovery omission. Reuse the upstream executable-body selector;
do not seed the generated helper, add manual companions or enlarge the unit
independently of discovered source provenance.

## Workaround

none

## Upstream tracking

none; upstream LCNF.toDecl already uses getDeclInfo?.

## Resolution and regression

One-site upstream executable-body selection passes the focused negative/positive
regression and all applicable production gates. Real renderer rebuilding now
includes the missing caller (90 roots versus 78), but still reports the same
unknown generated helper. This repairs a discovery omission, not the entire
capture failure; the remaining compiler-rebuild cause is unclassified. See
PROVENANCE_RESULT.md in the fixture. Runtime, source-unit policy and W6 are
unchanged; root review/acceptance is separate.

---
id: FIR-BUG-wasm-none-source-reset-inductive-metadata
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/ConstructorMetadata.lean
regression: integration/vbp-native-session-probe/ConstructorMetadata.lean
---

# Summary

Fresh source-unit reset hides defining-module mappings for constructor/native
extern roots, making their persisted LCNF metadata unreachable on Lean 4.34.

## Minimal reproduction

Apply `CompilerPrivate.forgetGeneratedCompilerModuleMappings` to imported
inductive/constructor roots. Their mappings disappear along with ordinary
function mappings. The renderer reaches this case with native extern `Int.ofNat`.

## Exact commands

With the pinned source view prepared and the 4.34-scoped Lake cache/TMPDIR
configured as documented in integration/vbp-native-session-probe/CONTROL.md:

```sh
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false env lean ConstructorMetadata.lean
FIR_RENDERER_CAPTURE=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Capture.lean
```

## Expected semantics

Reset function-body/specialization caches without losing the defining-module
identity of inductives and constructors. Lean computes their representation
metadata in that module; these are not stale function bodies to regenerate.

## Actual behavior

The generic reset unconditionally erases every source root's module mapping.
Constructor externs can enter source compilation while generating boxed
wrappers. Actual renderer tracing records `Int.ofNat` imported before reset
and local afterward, followed by the missing compiled-inductive diagnostic.

## Proof or differential evidence

The read-only metadata comparison passes before final dependency rebuilding.
Temporary exact-run tracing then records:

```text
FIR constructor reset: Int.ofNat; importedBefore=true importedAfter=false
`Int.ofNat` was not compiled; `compileDecls` must run on inductive types first
```

The generic regression fails before repair for Int, Nat, Option and all six
constructors. It also checks ordinary-function reset, so preserving every
mapping cannot satisfy the regression.

## Semantic impact

Source capture rejects otherwise compilable renderer code before Wasm
generation. No incorrect generated execution is established by this failure.

## Classification and triage

W7 capture adapter issue, not a missing Lean constructor or resident runtime
operation. Preserve type/constructor mappings; do not seed named metadata or
recompile inductives outside their defining modules.

## Workaround

none

## Upstream tracking

none; FIR removes the mapping that upstream metadata lookup requires.

## Resolution and regression

Generic preservation in CompilerPrivate passes the negative/positive metadata
regression and the production 4.33 checks. Actual ordinary renderer retry passes
this boundary and reaches an unknown generated Array.mapMUnsafe specialization;
no complete capture is claimed. See
integration/vbp-native-session-probe/REPAIR_RESULT.md and the lane handoff for
exact checks. Root acceptance remains separate. Runtime/proof/layout contracts
are unchanged.

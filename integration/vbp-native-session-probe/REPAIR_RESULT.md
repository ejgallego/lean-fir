# Fresh-unit constructor metadata repair

Date: 2026-09-15. Request: `ROOT-W7-20260915-002`. Production base:
`6c604d41f18b42db6e19059c8f4d954686b6cbe9`.

## Outcome

The generic mapping repair removes the observed `Int.ofNat` capture failure.
Actual ordinary renderer capture then stops at a **different generated-name
failure**, before returning a complete closure:

```text
Unknown constant `_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map._at_._private.Verso.Doc.0.Verso.Doc.ListItem.toJson.spec_0`
```

This is not a captured/linked renderer or a Wasm package. No completed
declaration, external or host inventory is available. Per the bounded request,
no successor repair, host classification, lowering/linking or runtime/proof
change is included.

## Mechanism and correction

The previous read-only comparison established that imported type metadata
was intact before `internalizeFinalDependencies`. Temporary tracing at the
actual fresh-unit reset then recorded:

```text
FIR constructor reset: Int.ofNat; importedBefore=true importedAfter=false
`Int.ofNat` was not compiled; `compileDecls` must run on inductive types first
```

`Int.ofNat` is both a constructor and a native extern. Constructor extern roots
can be encountered while recovering boxed adapters. The generic
`forgetGeneratedCompilerModuleMappings` erased all roots unconditionally,
including constructor/type module identities. Upstream's persisted metadata
lookup then could not find the imported entries.

The fix classifies constants using `ConstantInfo` and preserves defining-module
mappings for inductives and constructors in all erasure paths. Ordinary
function roots and owned generated declarations retain their previous reset
behavior. It does not initialize metadata, identify specific names, alter
source-unit grouping, or change deferred-module routing. The temporary trace
is removed; `Source.lean` is unchanged.

`ConstructorMetadata.lean` tests three imported inductives (`Int`, `Nat`,
`Option`) and all six constructors. It requires their mappings and public LCNF
metadata queries to survive, while the ordinary `List.length` root must lose
its mapping. The regression rejects the pre-fix implementation and accepts
the candidate. Names appear only as regression inputs, not in the repair.

Bug card: `FIR-BUG-wasm-none-source-reset-inductive-metadata`.

## Exact input identity

Consumer/toolchain/archive pins remain those in `RESULT.md`, `CONTROL.md` and
`SOURCE.json`: real `VersoBlueprint.Experimental.VirPreview.Renderer.render`,
Lean 4.34.0-rc2 revision `6a10ac8c22beadecabdbb0919c2b50214762f91d`, VBP
`c4430bfe2c898c0312903ae46c45b410d253ebf4`, VIR
`9fafe9cfd594213ee39dc8205b08084c31101816`, Verso
`52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9`, FIR source archive
`fdef2c1e44355367d449f26ecd87c0fd55a4319b`.

The single compiler overlay is `Fir/Wasm/Emit/CompilerPrivate.lean`, SHA-256
`3136b2a037ffa18ca83505f93ed9b08fac67e5f37d8d5a32a5927f9d78c1d916`.
`prepare.mjs` checks this hash and records it separately from the archive base.
The hash-checked dirty RPC overlay is unchanged. No consumer build products
or edits are involved. Production FIR remains on Lean 4.33.

Local diagnostic log identities:

- Traced pre-fix capture: `3651562af7fd1451aaf7083b684bbfffd305aad9b914fbd87415463f00caa0c3`.
- Actual repaired capture: `2d38d0fa644b6258f5b16793ed0d1ec00ff74ffc18f94d80eda9b34fdfa0ce0b`.

These logs are disposable working evidence under
`.deps/native-session-probe/control/`, not a permanent acceptance registry.

## Reproduce

From the W7 worktree:

```sh
export LAKE_CACHE_DIR="$(bash scripts/fir-lake-cache-path.sh)" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$PWD/.deps/native-session-probe/tmp"
node integration/vbp-native-session-probe/prepare.mjs
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false build Probe
lake --keep-toolchain -KpostponeCompile=false env lean ConstructorMetadata.lean
FIR_RENDERER_CAPTURE=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Capture.lean
```

The last command exits 1 with the new exact diagnostic above. Do not interpret
the successful `Probe` dependency build or metadata regression as full capture.
The fixture's postponed default and historical `check.sh` path remain unchanged.

## Checks

- Lean Beam: repaired `CompilerPrivate.lean` on both 4.33 and isolated 4.34;
  regression on 4.34; zero blocking diagnostics, saveReady. Sessions stopped.
- Regression negative control: pre-fix implementation rejects all nine
  metadata owners. Positive direct 4.34 and production 4.33 batch: pass,
  3 inductives/6 constructors.
- Ordinary `lake build Probe`: pass, 677 jobs (including reused jobs).
- Actual ordinary capture: expected stop at the newly reported diagnostic.
- `make check`: pass, 721 three-way cases plus 9 direct cases, 2,172 comparisons.
- `make talos-setup`, then `make talos-check`: pass, 3,205-job build and source/
  compiled trust audits. This does not remove existing recorded proof debt.
- `bash integration/talos/artifact/check.sh`: exit 0, including deterministic
  repeated source/prettyM generation, Node runtime checks and differentials.
  The stale Talos attestation took its normal successful 28-job fallback build.
  Browser/exhaustive checkpoint mode was not selected.
- Final `lake build Fir.Wasm.Emit.SourceExamples`: pass, 66 jobs.
- `prepare.mjs`, Node/bash syntax, bug-card validation (229 cards),
  `git diff --check` and `scripts/mailbox check`: pass.

No Beam save was used as final batch evidence. No benchmark, browser execution,
package/pointer movement, or performance claim is part of this repair.

## Next boundary

Root reviews this small generic fix first. A separate bounded investigation
should determine why final dependency rebuilding references the absent generated
specialization and preserve its true compiler-unit provenance. Its name alone
does not establish whether discovery, cache isolation or companion retention
is at fault. Do not preemptively seed that name or broaden compilation units.

# Constructor metadata survives ordinary capture

Request `ROOT-W7-20260915-001`, 2026-09-15, exact base
`b1cbd6677806fd4122368025cdefd9d410aadd38`. Frozen inputs remain unchanged.
This narrows [the capture failure](CAPTURE_RESULT.md); it does not fix it.

## Decisive comparison

The ordinary imported environment and the environment immediately before
`internalizeFinalDependencies` give **identical successful query results**:

| Public query / visibility | `Int` | `Int.ofNat` |
| --- | --- | --- |
| Source module | `Init.Data.Int.Basic` | `Init.Data.Int.Basic` |
| Constant present | yes | yes |
| Native IR declaration present | no (type) | yes |
| `LCNF.getOtherDeclBaseType` | `Type` | `Nat -> Int` |
| `LCNF.getOtherDeclMonoType` | `lcErased` | `Nat -> Int` |
| `LCNF.nameToImpureType` | `tobj` | not applicable |
| `LCNF.getCtorLayout` | not applicable | tag 0, one object field, zero USize/scalar bytes |

Therefore no missing metadata fact is observable at the two requested
boundaries. In particular, constructor mono type and layout were not lost by
the individual-entry or external-boxed-adapter stage. The earlier failure
occurs **inside the subsequent fresh-unit dependency rebuild**, not in ordinary
Lean compilation or the initial imported environment.

The pre-final artifact has 1,895 declarations and 125 externals. `Int.ofNat`
and `Int.negSucc` are externals there. Of the 78 source roots listed in the
previous failure, 36 already appear as declarations and none as exact external
names; generated external descendants can still require those source owners.
This is evidence of remaining dependency work, not permission to skip it.
These counts are **not** a completed final closure or host frontier. No host
binding classification was attempted.

## Diagnostic and checks

`Probe.captureBeforeFinal` merely exposes the existing first two stages;
`Probe.capture` still runs exactly the original sequence. `Metadata.lean`
reads the public queries under `withoutModifyingEnv`, catches query failures
as data, and records both snapshots plus pre-final declaration/external names.
It never calls `internalizeFinalDependencies`, a metadata initializer, an
inductive compiler, or a fix. No source archive or production code was changed.

Using the existing worktree-local 4.34 cache and TMPDIR setup in CONTROL.md,
run from `integration/vbp-native-session-probe`:

```sh
lake --keep-toolchain -KpostponeCompile=false build Probe
FIR_RENDERER_METADATA=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Metadata.lean
```

Both exit 0. Probe and Metadata Beam update/sync pass with zero blocking
diagnostics and saveReady; session stopped before batch execution. No Beam
save substituted for the final focused build. The explicit environment switch
keeps editor checking separate from executing capture stages. Node/bash syntax,
diff and mailbox checks pass. Broad gates were excluded by root's bounded scope.

Local disposable evidence:

- `.deps/native-session-probe/metadata/imported.json`;
- `.deps/native-session-probe/metadata/comparison.json`, SHA-256
  `140c042d87c41394418978781f0dbd3400de0e9db13064bb8aa53895f7433d33`;
- `.deps/native-session-probe/control/metadata-batch.log` and
  `metadata-beam.json`.

## Smallest next repair investigation

Trace metadata visibility inside `compileEntryFinalCapturedInternalized` and
its source-root discovery/cache-reset boundary. W7 owns the relevant
`Source.lean` / `CompilerPrivate.lean` machinery; there is no evidence for a
W6 runtime or Lean `Int` implementation change. The exact failing query/site
inside that rebuild remains unobserved: do not claim a root cause merely from
the shared diagnostic wording.

Upstream marks `Int.ofNat` and `Int.negSucc` as native externs even though they
are constructors. Any future source-root/cache-reset repair must preserve that
distinction and their defining-module metadata; this is a lead, not a tested
fix. No compiler patch, workaround, full-capture retry, lowering, linking,
Wasm, consumer update, package publication or W6 task is part of this slice.
Bug cards: none; no established semantic discrepancy or workaround.

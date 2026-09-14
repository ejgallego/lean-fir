# Ordinary versus postponed compilation control

Date: 2026-09-14. Request: `ROOT-W7-20260913-004`. Base:
`65360510826b50939a7731c2cdb397a3368bfd97`. This is a diagnostic checkpoint,
not a Wasm package or full-capture result. All source/toolchain identities in
[RESULT.md](RESULT.md) are unchanged.

## Result

| Check | Observed result |
| --- | --- |
| `VersoBlueprint.Html`, postponement true | Exit 1 in `leanir`: unknown `String.Slice.posGE._redArg` while compiling `escapeText` |
| Same target/source, postponement false | Exit 0, 282-job build |
| Ordinary `+Probe:deps` | Exit 0, 676-job dependency cone |
| Ordinary `Probe` | Exit 0, 677-job build; missing-module-header warning |
| Read-only renderer metadata | Source constant, source module, impure signature and native IR present; zero deferred groups |
| Lean Beam | Lakefile and final metadata probe: zero blocking diagnostics, saveReady; session stopped |
| Direct batch metadata probe | Exit 0, same metadata as Beam |

Both actual `Html.setup.json` files have identical option maps except
`compiler.postponeCompile`. The control asserts this and the unchanged source
hash; it does not infer success merely from the requested command-line flag.
`experimental.module=true` is retained in both runs.

- HTML source SHA-256:
  `5d18ab81dbb9dfbd931fb38b373deb57344fc6559359d3410b8b5ca87b9fccb5`.
- Postponed setup SHA-256:
  `36e519059cd0cd696bdd7d882945cf56b0ea648ed82ea8504063fa99b66d846f`.
- Ordinary setup SHA-256:
  `55e0eb3b7479b2eacba065516194b3e4aa9a25a2729cace41627350312fbc377`.

The exact metadata is:

```json
{
  "entry": "VersoBlueprint.Experimental.VirPreview.Renderer.render",
  "module": "VersoBlueprintVir.Preview.Renderer",
  "isSourceConstant": true,
  "hasImpureSignature": true,
  "hasNativeIR": true,
  "deferredGroups": 0
}
```

`Classify.lean` only reads module products. It imports with `loadExts=false`
to avoid executing initializers; compiler signatures and IR are read from
their persisted entries. No renderer recompilation or capture happens in this
query. Two initial probe-scaffolding corrections (command syntax/namespace and
avoiding initializer execution) are not additional consumer failures.

## Reproduce

From the W7 worktree, with the frozen archives prepared as in RESULT.md:

```sh
export LAKE_CACHE_DIR="$(bash scripts/fir-lake-cache-path.sh)" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$PWD/.deps/native-session-probe/tmp"
node integration/vbp-native-session-probe/control.mjs
lake +leanprover/lean4:v4.34.0-rc2 -d integration/vbp-native-session-probe --keep-toolchain -KpostponeCompile=false build +Probe:deps
lake +leanprover/lean4:v4.34.0-rc2 -d integration/vbp-native-session-probe --keep-toolchain -KpostponeCompile=false build Probe
lake +leanprover/lean4:v4.34.0-rc2 -d integration/vbp-native-session-probe --keep-toolchain -KpostponeCompile=false env lean integration/vbp-native-session-probe/Classify.lean
```

The control runs these two commands inside the fixture directory:

```sh
lake --keep-toolchain --reconfigure -KpostponeCompile=true build VersoBlueprint.Html
lake --keep-toolchain --reconfigure -KpostponeCompile=false build VersoBlueprint.Html
```

It deliberately expects the first command to fail with the recorded missing
helper. A future upstream fix should require reviewing that assertion, not
silently preserving the old negative expectation. The fixture default remains
true. No production setup or consumer manifest changed.

Local disposable logs, copied setup files and `controls.json` are under
`.deps/native-session-probe/control/`. The ordinary command output counts
include replayed jobs; they are not compilation-time measurements. No Beam save
was used as batch evidence. Node/bash syntax checks, diff check and mailbox
validation pass. Broad make/Talos/artifact/browser gates were deliberately not
run under root's explicit bounded-control instructions.

## Interpretation and next boundary

Lean 4.34's `compiler.postponeCompile` option defaults to false and is described
in `Lean/Compiler/Options.lean` as the internal experimental `leanir` separate
compilation toggle. The A/B test isolates this fixture's failure to that path,
not an ordinary source/frontend failure. The ordinary generated HTML C also
declares the requested `l_String_Slice_posGE___redArg` external. This does not
establish the exact upstream cause of the postponed replay failure.

The frozen FIR `Source.lean` source-unit resolver uses source-constant
membership, module identity and `getImpureSignature?`; these inputs are present.
Its deferred capture path returns `none` when groups are empty, and its existing
individual-source entry then falls back to ordinary source capture. These are
source-level routing facts, not an executed capture result.

The smallest proposed follow-up is to run actual capture for the same renderer
through that existing ordinary-source path, preserving source-unit boundaries
and stopping at the first diagnostic. Do not add generated-name shims, change
the renderer, or expand the host profile. Root must review this checkpoint
before that next slice. No LCNF closure, Wasm, import frontier, profile verdict,
browser evidence or performance claim was produced here. W6 and runtime/proof
contracts are untouched. No semantic discrepancy or workaround was established;
bug cards: none.

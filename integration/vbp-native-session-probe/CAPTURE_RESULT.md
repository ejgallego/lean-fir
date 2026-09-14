# Ordinary-source renderer capture: dependency-rebuild blocker

Request: `ROOT-W7-20260914-001`. Run: 2026-09-14, checkpoint report 2026-09-15.
Base: `174d5aee1f4023e8251c98cd6e5502e90949641c`. Exact frozen compiler,
toolchain, VBP/VIR/Verso and dirty-RPC identities remain those in
[RESULT.md](RESULT.md). The previous [A/B control](CONTROL.md) is unchanged.
This is a failed capture investigation, not a generated artifact.

## Outcome

`Probe` builds successfully (677 jobs including replayed dependencies).
`Capture.lean` passes Beam with zero diagnostics and saveReady=true. Beam was
stopped before the actual batch capture; no Beam save supplied build evidence.

Batch capture exits **1**, after entering the existing `NativeSessionProbe.capture`:

```text
Renderer: ordinary-source capture begin
Capture.lean:41:0: error: Failed to rebuild unresolved source closure [Lean.Name.toString,
 ...
 Lean.Vir.Js.Array.ofArray]
  `Int.ofNat` was not compiled; `compileDecls` must run on inductive types first
```

The diagnostic contains 78 dependency root names, including the renderer's
private inline/block renderers, JSON instances, String/Array operations,
`Std.Format.prettyM` and VIR props/array builders. **78 is the size of the
reported dependency-rebuild request, not a captured declaration count or a host
import count.** Complete local log:
`.deps/native-session-probe/control/capture-batch.log`, SHA-256
`11019a3a6a3487848798ed39cffcf5776a6d726b1f4dc5e198a612dbcd7fa4f5`.

No `captured.lcnf` or `capture.json` was written. The driver writes these only
after `NativeSessionProbe.capture` returns. Final declaration/host counts and
names, LCNF hash and render-core/v0 verdict are therefore **unavailable**, not
zero. No profile descriptor was guessed from imported metadata alone.

## Location and interpretation

The exact diagnostic prefix comes from the frozen FIR
`Fir/Wasm/Emit/Source.lean`'s `internalizeFinalDependencies` (line 1155).
This is the third stage already present in `Probe.capture`, after individual
entry internalization and boxed-adapter recovery. It rebuilds unresolved roots
in a fresh compiler unit; the failure is not the earlier missing-module lookup
or postponed `String.Slice.posGE._redArg` failure.

Lean's LCNF type code emits the final diagnostic when expected precompiled
inductive/constructor metadata is absent. Several type-processing sites emit
that wording, so the message alone does not identify which extension lookup
failed or why it was unavailable. Ordinary compilation still succeeds. This
is a capture/environment-preparation boundary to investigate, not evidence
that the renderer source or the definition of `Int.ofNat` is invalid.

The next narrow investigation should inspect the necessity and source-unit
semantics of that final dependency-rebuild stage for this ordinary individual
capture, and trace the missing constructor metadata in its fresh environment.
Do not merge extra source units or add a named shim to silence the error.
This report does not implement a fix or authorize a shared compiler change.

## Exact reproduction and checks

From the W7 worktree with the accepted archives already prepared:

```sh
export LAKE_CACHE_DIR="$(bash scripts/fir-lake-cache-path.sh)" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$PWD/.deps/native-session-probe/tmp"
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false build Probe
FIR_RENDERER_CAPTURE=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Capture.lean
```

The capture driver also sets `compiler.postponeCompile=false` around the actual
command. The generated renderer setup confirms ordinary mode with
`experimental.module=true`. Frozen renderer and RPC hashes were rechecked:

- Renderer: `f71035bbed37d779db8efdd77c4a4f471512efd2f01daa5008ff682e43230926`.
- RPC delta: `b11a19b76283fec7137c2ea623b94b178dbae29095ec41a775c2045781d30ea6`.

`SOURCE.json` retains the earlier archive-preparation fixture head; it identifies
the unchanged inputs, not this later driver checkpoint. Git and the exact lane
handoff identify the new driver. Local logs are disposable working evidence.

`Capture.lean` separates driver elaboration from execution using the explicit
`FIR_RENDERER_CAPTURE=1` switch. Without it, Beam can validate the driver without
writing evidence or rerunning capture. Success would record raw captured LCNF
types and Lean borrow flags, **not** invent host resource ownership from those
flags. Profile review would remain a distinct step.

Focused `lake build Probe`, Beam driver checks, Node/bash syntax, diff and
mailbox validation pass; actual capture fails exactly as above. Per root's
stop-at-first-diagnostic scope, no lower/link/encoding, broad make/Talos gate,
browser, adapter or W6 work ran. No consumer source, production compiler,
runtime, proof, profile, package, pointer or remote branch changed.
Bug cards: none; no semantic discrepancy established and no workaround added.

---
id: FIR-BUG-wasm-none-format-closure-coordinate-ratchet
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.34.1
lean-revision: 5045d0056413266e57c625dcd7c365b10e377c52
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-10-08
reproduction: integration/talos/artifact/FirWasmSourceExample.lean
regression: integration/talos/artifact/FirWasmSourceExample.lean
---

# Summary

The complete artifact gate's resident Format closure-projection ratchet expects
twelve source coordinates, but fresh accepted source capture produces eight.

## Minimal reproduction

Fresh source capture in the run_cmd starting at line 277 of FirWasmSourceExample.
The exact inventory assertion is at line 389 onward.

## Exact commands

With the repository Lake cache configured and TMPDIR worktree-local:

```sh
FIR_BROWSER=google-chrome FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 \
  bash integration/talos/artifact/check.sh
```

The gate's focused command is:

```sh
cd integration/talos/artifact
FIR_PRETTYM_CHECKPOINTS=1 lake env lean FirWasmSourceExample.lean
```

## Expected semantics

The current ratchet requires 104 operations covering all twelve entries of
ResidentRuntime.prettyFormatSourceClosureProjectionCoordinates.

## Actual behavior

104 operations are captured, with eight distinct coordinates: tobject fields
0 through 4, uint8 fields 0 and 1, and uint32 field 1. The expected object-kind
fields 0 through 4 are absent; tobject field 4 is new relative to the expected
coordinates. The gate rejects before linked/browser checks.

## Proof or differential evidence

Full gate failed at FirWasmSourceExample.lean:277:0; diagnostic names the
resident Format closure-projection inventory. Local checkpoint ac09d451d changed
only tooling/talos-434; Fir/Wasm and artifact sources match base 15dc1f460.
The source fixture imports FIR capture/emission modules, not FirTalos proofs.
Failure log SHA-256:
7571ff009d660d0109af426809d7024adcb4278f308f8221000ffe3233f5fbd0.

## Semantic impact

The stale guard prevented the artifact gate from reaching engine and browser
checks. No wrong generated Wasm observation was established.

## Classification and triage

Accepted-main `15dc1f460` with the old Talos overlay fails identically under
the checkpoint flag. Candidate and control have identical projection imports,
closure descriptor/dispatch tables and captured LCNF (SHA-256
2a2db2e233c6fa3e94e241016e8e6aaed2f253a919eb56cae48085036fd71ca5).
This is a validation-harness error, not Talos-dependent source capture drift.

Accepted compiler policy `closureProjectionKind`, introduced by `645907212`,
widens object-like projection results to tobject while retaining stored raw
descriptor kinds. The guard compared that normalized runtime result inventory
against the twelve raw source-capture coordinates. Canonicalizing those expected
coordinates produces exactly the observed eight, including index 4's tobject.
No compiler, runtime, descriptor layout or ABI change is required.
The checkpoint flag is required: the default fixture path returns after the
basic Format products and does not execute the resident inventory guard.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The fixture canonicalizes/deduplicates expected source coordinates through the
existing compiler policy, keeping the 104-operation ratchet, bidirectional
coverage, stable descriptor/dispatch and helper-export checks. Three negative
probes reject same-count wrong result kinds, same-count missing coordinate
coverage and a dropped operation. The companion JS artifact checker derives
its complete helper-export set from the producer's pre-link projection imports,
instead of hardcoding obsolete object result aliases, and rejects both missing
and extra helper exports. The focused Lean fixture and JS resident-family
checker pass. The full gate advances past this guard and the resident-family
checker, then stops at the separately recorded host descriptor lifetime defect.
The repair changes validation only; emitted executable bytes are unchanged.

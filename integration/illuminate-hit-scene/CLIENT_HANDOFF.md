# Provisional HitScene compiler demo handoff

This handoff lets compiler and Illuminate clients reproduce FIR admission and
symbolic lowering of the real prepared hit-scene query while the W6 proof owner
checks the lazy-cache result-kind refinement. It is intentionally not a Wasm
package handoff.

## Revisions and status

- FIR integration branch: `integration/hitscene-admission`
- FIR contract candidate: `c93bf226`
- FIR diagnostic successor: `14242c49`
- FIR contract base on `main`: `0792847b`
- Illuminate source: clean detached commit
  `af088e313eaade90be100aeaf63ddac79a8c1710`
- Lean toolchain: `leanprover/lean4:v4.32.0`
- Source entry: `Illuminate.HitScene.query`
- Status: demo-ready on the integration branch; not landed or proof-accepted

Resolve the current containing handoff commit from the named integration
branch. The functional compiler identity is the fixed contract candidate above.

## Reproduce

Create the clean source view once if it does not already exist:

```sh
git -C /home/egallego/lean/illuminate worktree add --detach \
  /tmp/illuminate-hit-scene-pinned \
  af088e313eaade90be100aeaf63ddac79a8c1710
```

Run the exact source capture and lowering probe from the FIR integration
worktree:

```sh
cd /home/egallego/lean/fir/.worktrees/integration-hitscene-admission/integration/illuminate-hit-scene

lake --keep-toolchain --reconfigure \
  -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  build IlluminateFirHitScene.Compile

lake --keep-toolchain \
  -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  env lean -DmaxHeartbeats=0 Probe.lean
```

The probe may take roughly one to two minutes and several gigabytes of peak
memory because it captures the complete final-LCNF closure and formats the
full symbolic source artifact.

## Expected result

The final log line reports:

```text
captured 159 HitScene declarations with 34 externals and 0 unsupported declarations
```

Inspect the stable summary with:

```sh
jq '{unsupportedDeclarations, runtimeOperations, baseFunctions, loweringError}' \
  _build/hit-scene-probe.json
```

Expected values:

```json
{
  "unsupportedDeclarations": [],
  "runtimeOperations": 311,
  "baseFunctions": 126,
  "loweringError": null
}
```

The reference outputs from the candidate run have these SHA-256 digests:

```text
fa08b94db107dce57202532500df60c1b9180e9679c0aeb814f0e4861b0f475f  _build/hit-scene-probe.json
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  _build/hit-scene-unsupported.lcnf
476fec8fe1c2ed9bf89f9848e90ddb0bd2f0b385c32e8b1072246776f838209c  _build/hit-scene-partial-application.lcnf
```

Capture/lowering timings in the JSON-producing run are diagnostic and are not
part of the deterministic identity.

## What clients can test now

- the exact Lean 4.32 source view and entry name;
- final-LCNF closure capture without copying Illuminate logic into FIR;
- admission of the generated boxed-Float partial application;
- complete symbolic lowering and runtime-operation inventory;
- absence of unsupported declarations or a lowering error;
- the exact relevant LCNF declarations recorded by the probe.

## Deliberately unavailable in this handoff

- an `illuminate-hit-scene.wasm` binary;
- resident implementations of the 34 external names;
- a JavaScript input/output adapter;
- external-engine or differential execution;
- a stable input layout or memory-ownership contract;
- proof acceptance of the refined lazy-cache result kind.

Do not point Illuminate staging scripts at this directory: it does not satisfy
the immutable package contract. Once W6 returns a green cache proof and the
candidate lands on `main`, W7 can use this admitted closure as the input to the
resident-linking and client-package slice.

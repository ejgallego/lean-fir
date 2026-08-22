# Steady-state Node CPU profiles

`node-profile.mjs` collects a diagnostic V8 CPU profile for an exact stripped
FIR Wasm artifact. Setup and an honest checked first call occur before the
profiler starts. Only the workload's `steady` operation is sampled. This is a
separate diagnostic run, never a headline timing sample.

The workload module exports:

```javascript
export const metadata = { id: "client/workload" };
export async function setup(context) { return state; }
export async function firstCall(state, context) {
  return { ok: true, observation: { digest: "..." } };
}
export async function warmup(state, context) {
  return { ok: true, observation: { digest: "..." } };
}
export async function steady(state, context) {
  return { ok: true, observation: { digest: "..." } };
}
export async function teardown(state, context) {}
```

`firstCall`, optional `warmup`, and `steady` must validate their semantic result
and return `ok: true`; otherwise profiling fails without publishing partial
evidence. The optional warmup is timed and retained but runs before sampling.
`context` supplies copied Wasm bytes, the validated function sidecar, the
artifact path, and its hash. The sidecar view is recursively frozen; the
collector reparses its authoritative bytes before deriving attribution. The
driver owns the package ABI and input corpus.

For comparable evidence, provide a small workload receipt. Paths are relative
to the receipt, roles are unique within each list, and every listed file is
hashed before the workload starts and checked again after teardown:

```json
{
  "schemaVersion": "fir.profile-workload-receipt/v1",
  "id": "client/workload",
  "semanticEndpoint": "checked result digest and terminal state",
  "instancePolicy": "fresh-instance-per-profile",
  "parameters": { "rounds": 50000000 },
  "dependencies": [
    { "role": "browser-adapter", "path": "package/adapter.mjs" }
  ],
  "inputs": [
    { "role": "representative-corpus", "path": "inputs/corpus.json" }
  ]
}
```

The receipt is deliberately an identity declaration, not a workload catalog.
It must name every imported driver/adapter file and input whose contents affect
the sampled operation. A capture without a receipt remains usable as screening
evidence but is not eligible for a default multi-run aggregate.

```text
node tooling/profile/node-profile.mjs \
  --wasm package/app.wasm \
  --sidecar package/app.wasm.functions.json \
  --workload client/profile-workload.mjs \
  --workload-receipt client/profile-workload-receipt.json \
  --out-dir _build/profile
```

The output directory is published atomically and must not already exist. It
contains the untouched `profile.cpuprofile` and a derived `evidence.json`.
The `fir.sampled-profile/v2` evidence binds the Wasm, sidecar, driver, declared
dependencies and inputs, Node/V8 and host shape, sampling interval, phase
timings, checked observations, and raw profile hashes. Optional metadata files
are also hashed and checked for mutation. The comparability key covers the
content identities and semantic/runtime dimensions rather than filesystem
locations.
V8 begins sampling before the `Profiler.start` response returns, so the raw
profile also contains that protocol handshake. Derived attribution crops by
the recorded sample `timeDeltas` to the measured steady window; the raw profile
remains authoritative and permits recomputation. Exact evidence fails closed
when `timeDeltas` are absent or malformed. Unbound raw-profile inspection may
use an explicitly labeled uniform-interval approximation.

Each capture includes a structural quality classification and raw diagnostics
such as included sample count, Wasm/host sample counts, sampled microseconds,
and Wasm-self share. A checked capture currently requires at least 100 Wasm
self samples; smaller captures remain valid but are labeled
`low-wasm-self-sample-count` screening evidence. This is an attribution-quality
floor, not a performance pass/fail threshold.

Derived self time is grouped into retained Lean code, allocation,
reference-counting, boxing/unboxing, Array, String, numeric,
projection/update, other resident support, linked/optimizer Wasm, and
host/unattributed frames. Unknown functions remain explicit.

Tooling scratch stays under the active FIR worktree's
`.deps/tooling-tmp/`. Set `FIR_TOOLING_TMPDIR` only to choose another
subdirectory of that same worktree-local `.deps`; paths outside it are
rejected. The requested profile output remains caller-owned and is staged
beside its final location before an atomic rename.

Pure attribution and malformed-profile tests run in the fast tier:

```sh
make -C tooling unit-check
```

The live inspector/CLI test uses the pinned Binaryen fixture and belongs to the
explicit external tier:

```sh
make -C tooling profile-check \
  FIR_BINARYEN_DIR=/path/to/emscripten-5.0.3/upstream/bin
```

The live test verifies artifact/sidecar/workload immutability, raw evidence
hashes, resolved Wasm samples, checked phase observations, and absence of
partial output after an unchecked steady result. It also passes the captured
profile through aggregate v2, checks complete per-function caller coverage,
and requires the real `Fixture.entry` to `Fixture.leaf` Wasm caller edge. The
gate never downloads tools and never skips when its dependency is missing.

## Cross-run final-function resolver

`profile-aggregate.mjs` re-derives attribution from one or more untouched raw
profiles and compares only evidence bound to the same exact release Wasm and
verified final-function sidecar:

```sh
node tooling/profile/profile-aggregate.mjs \
  --wasm package/app.wasm \
  --sidecar package/app.wasm.functions.json \
  --evidence _profiles/run-1/evidence.json \
  --evidence _profiles/run-2/evidence.json \
  --out _profiles/aggregate.json
```

Legacy or externally collected V8 profiles may be supplied with repeated
`--profile FILE` arguments. Because a raw `.cpuprofile` does not embed the Wasm
digest, those runs and the aggregate are explicitly labeled unbound even though
the selected Wasm and sidecar are verified and all indices resolve. Prefer
`--evidence` for new captures.

The `fir.sampled-profile-aggregate/v3` report groups duplicate V8 nodes by
absolute final function index. It retains per-run self samples, sampled
microseconds, normalized Wasm-self share, and rank; cross-run fields report the
median, median absolute deviation, range, and rank span. Exact name, origin,
family, and body bytes come only from the verified sidecar. Host samples remain
visible at run level, while a Wasm index outside the complete sidecar is
rejected as malformed.

Each sampled Wasm leaf is also attributed to its immediate parent node in the
V8 CPU-profile tree. Per-function `callers` retain recursive Wasm callers,
host/runtime function-and-URL frames, and a root bucket rather than guessing
across missing frames. Each edge reports its share of total Wasm self samples
and, conditional on the target being sampled in a run, its share of that
target's self samples.
The aggregator rejects duplicate node ids, missing or multiply-parented
children, parent cycles, and caller indices outside the exact sidecar. This is
sampled caller evidence, not a dynamic call count or an inclusive-time metric.

With two or more runs, the command also requires the same v2 comparability key:
workload module, receipt, dependency/input identities, workload metadata,
checked observations, Node/V8, platform/architecture, and sampling interval
must match. Legacy v1 evidence, receipt-free evidence, unbound raw profiles,
and key mismatches are rejected by default. `--allow-incomparable` is an
explicit exploratory escape hatch; its report is marked
`incomparable-override` and `screening`, never comparable evidence. A single
run is likewise marked screening rather than replicated evidence.

The command refuses mixed artifacts, sidecars, duplicate input paths, raw
profile hash mismatches in bound evidence, missing exact-profile time deltas,
empty Wasm windows, and output reuse. It does not
rewrite, copy, or delete the caller-owned raw evidence. Sample shares are noisy
diagnostic attribution and must not be presented as headline elapsed-time
measurements.

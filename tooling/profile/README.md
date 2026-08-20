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
artifact path, and its hash. The driver owns the package ABI and input corpus.

```text
node tooling/profile/node-profile.mjs \
  --wasm package/app.wasm \
  --sidecar package/app.wasm.functions.json \
  --workload client/profile-workload.mjs \
  --out-dir _build/profile
```

The output directory is published atomically and must not already exist. It
contains the untouched `profile.cpuprofile` and a derived `evidence.json`.
Evidence binds the Wasm, sidecar, driver, Node/V8 version,
sampling interval, phase timings, checked observations, and raw profile hashes.
V8 begins sampling before the `Profiler.start` response returns, so the raw
profile also contains that protocol handshake. Derived attribution crops by
the recorded sample `timeDeltas` to the measured steady window; the raw profile
remains authoritative and permits recomputation.

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
partial output after an unchecked steady result. The gate never downloads
tools and never skips when its dependency is missing.

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

The `fir.sampled-profile-aggregate/v1` report groups duplicate V8 nodes by
absolute final function index. It retains per-run self samples, sampled
microseconds, normalized Wasm-self share, and rank; cross-run fields report the
median, median absolute deviation, range, and rank span. Exact name, origin,
family, and body bytes come only from the verified sidecar. Host samples remain
visible at run level, while a Wasm index outside the complete sidecar is
rejected as malformed.

The command refuses mixed artifacts, sidecars, duplicate input paths, raw
profile hash mismatches in bound evidence, empty Wasm windows, and output
reuse. It does not
rewrite, copy, or delete the caller-owned raw evidence. Sample shares are noisy
diagnostic attribution and must not be presented as headline elapsed-time
measurements.

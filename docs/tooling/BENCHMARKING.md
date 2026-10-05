# FIR benchmarking and profiling boundary

FIR owns evidence about the compiler artifact. It does not own a copy of each
client's workload catalog or a second browser benchmark framework.

## Catalog and ownership

| Evidence | Durable owner | FIR's role |
|---|---|---|
| Release Wasm identity, final-function sidecar, bounded function view | FIR tooling/package producer | Bind every observation to the exact optimized bytes and keep unknown linked functions explicit. |
| Checked steady CPU profile | FIR tooling | Sample only after setup, the honest first call, and warmup; retain the raw profile separately from headline timings. |
| Instruction-level Wasm profile | FIR tooling | Join a supported engine's source coordinates to FIR instruction origins without changing release bytes. |
| Compiler mechanism probe | FIR tooling | Ratchet a narrow semantic or cost-shape invariant using ordinary compiled Lean. |
| Production corpus and semantic oracle | lean-zip, Illuminate, Verso, or another client | Select optimization targets and confirm them on real inputs. |
| Browser campaigns, process isolation, aggregation, and reports | VIR benchmark catalog | Compare backends without making FIR depend on VIR or vendoring VIR into FIR. |

The interchange boundary is an immutable artifact plus versioned JSON or JSONL
evidence. FIR and VIR remain independent repositories; neither is a submodule
of the other.

## Evidence rules

Correctness gates and performance evidence are separate. CI may ratchet exact
outputs, import/export contracts, ownership, and qualitative allocation shape,
but a hosted runner's duration is not a performance conclusion.

A performance record contains at least:

- FIR, Lean, workload, and client revisions, including dirty/source hashes;
- Wasm and function-sidecar byte lengths and SHA-256 values;
- source entry, ABI/layout/ownership versions, imports, and exports;
- input family, dimensions, seed, input hash, and checked output hash;
- engine version, host architecture, timing clock, and profiler state;
- setup, first-call, warmup, measured rounds, order, and instance policy; and
- raw samples or the untouched CPU profile beside any derived summary.

Paired headline comparisons use the same semantic endpoint and phase boundary,
exclude warmups, alternate order, retain every measured row, and report median,
dispersion, and order effect. A raw FIR Wasm entry call is not compared with a
wider `runtime.call` interval. Profilers and optional diagnostic counters run
outside headline timing rounds.

Use the common phase names `acquire`, `compile`, `instantiate`, `initialize`,
`firstCall`, `warmup`, `project`, `encode`, `execute`, `decode`, `rewind`, and
`total`. Mark absent phases absent instead of folding them into another phase.
Memory evidence records the persistent checkpoint, peak and post-rewind
frontiers, persistent growth, and linear-memory pages when available.

## Current FIR surfaces

- [`tooling/wasm/`](../../tooling/wasm/README.md) validates an
  artifact-hashed final-function sidecar and emits a bounded view of one
  optimized function and its direct call neighborhood.
- [`tooling/profile/`](../../tooling/profile/README.md) captures a checked,
  steady-only Node/V8 profile and binds the raw profile and derived attribution
  to the exact Wasm, sidecar, workload receipt, declared dependencies, and
  inputs. Its cross-run resolver rejects incompatible semantic/runtime
  identities by default, folds V8 nodes by final function identity, attributes
  sampled leaves to their immediate caller nodes, and reports structural
  quality, per-run shares, median, dispersion, and rank stability without
  treating profiler time as a headline benchmark.
- [Exact-release Wasm caller attribution](WASM_CALLER_ATTRIBUTION.md) records
  the first production prettyM and lean-zip caller census and its limitations.
- [`tooling/array-probe/`](../../tooling/array-probe/README.md) compiles ordinary
  Lean through the production FIR pipeline and distinguishes repeated reads,
  allocation, unique updates, and shared copy-on-write. It is a mechanism
  ratchet, not a production benchmark or target selector.
- [Array runtime history](ARRAY_RUNTIME_HISTORY.md) records the implementation
  boundary that motivated the probe.
- [Wasm instruction profiling](WASM_INSTRUCTION_PROFILING.md) records the
  selected `d8`/perf consumer and the limits of Node's current source-map path.

Run dependency-free tooling checks with `make tooling-unit-check`. Run the
complete pinned-Binaryen and compiled-probe gate with `make tooling-check`.
The [external tooling CI contract](CI.md) fixes the supported Node LTS matrix,
dependency boundary, and fail-closed provider-neutral job behavior.

## Measurement workflow

Start with a current accepted recipe from [build-examples.md](../build-examples.md)
and its real client workload. The client supplies inputs and the checked
semantic endpoint. A package producer supplies the executable, adapter and
verified function sidecar. Use the same inputs, output/styling normalization,
instance lifetime and measured interval for each compared backend.

Keep these four boundaries explicit:

| Question | Measure | Evidence |
| --- | --- | --- |
| How long does building the package take? | The public recipe command; distinguish provisioning, a no-change build and a source-invalidated build | Source/compiler identities, cache policy, affected Lake jobs, wall/user/system time and RSS |
| How long does loading take? | Acquire bytes, WebAssembly compilation, instantiation and initialization | Package hash, engine/version, cache and module-sharing policy |
| How long does an operation take? | Projection, encoding, raw execution, copied decoding and any rewind; independently time the complete call | Raw unprofiled samples, checked output, warmups/order and memory frontiers |
| Why is execution expensive? | A separately captured checked steady profile | Exact executable/workload binding, raw CPU profile, sampled self/caller attribution and explicit unknowns |

A timing field called `compile` needs its context: compiling Lean source and
`WebAssembly.compile` are different operations. A recipe acceptance command
may include native-oracle tests; its total is not pure compiler time. A direct
binary invocation excludes Lake planning/build work. Likewise, a raw FIR export
call is narrower than an adapter or VIR `runtime.call` interval.

For build/check latency, use the existing
[throughput procedure](CHECK_THROUGHPUT.md). Provision first for warm samples,
record exactly what a source edit invalidates, and collect frontend/Lake evidence
before choosing native runtime profiling. Do not optimize a fixture based only
on another project's profile.

For an operation comparison, run the client's existing timing harness with
diagnostics off, matched endpoints, excluded warmups and balanced backend order.
Keep each measured row, including phase values, complete-call wall time and
frontier growth. Report median and dispersion; phase medians need not sum to
the total median. Instance reuse and linear-memory reclamation belong in the
comparison contract. A monotonic arena requires bounded fresh-instance batches
or explicitly reported accumulated growth.

For attribution, provide a driver and workload receipt using the existing
[collector contract](../../tooling/profile/README.md). With caller-supplied
release/sidecar and client files, the commands are:

```sh
node tooling/wasm/function-index.mjs verify \
  --wasm package/app.wasm --sidecar package/app.wasm.functions.json
node tooling/profile/node-profile.mjs \
  --wasm package/app.wasm --sidecar package/app.wasm.functions.json \
  --workload client/profile-workload.mjs \
  --workload-receipt client/profile-workload-receipt.json \
  --out-dir .deps/profiles/run-1
```

Collect a second capture to a fresh directory with the same semantic/runtime
identity, then aggregate the bound evidence:

```sh
node tooling/profile/profile-aggregate.mjs \
  --wasm package/app.wasm --sidecar package/app.wasm.functions.json \
  --evidence .deps/profiles/run-1/evidence.json \
  --evidence .deps/profiles/run-2/evidence.json \
  --out .deps/profiles/aggregate.json
```

Resolve a hot function with `function-index.mjs inspect` or `view`; route
runtime/lowering changes to W7 and changed proof contracts to W6. Source-level
ownership conclusions need the real generated LCNF/C and caller path.
Use instruction-origin/`d8` diagnostics only when function/caller attribution
does not answer the question. Profiler shares remain attribution, not elapsed
time or an application speedup.

## Consolidation priorities

Use one client-owned representative harness per workload. Keep preparation,
timing and result normalization beside its recipe/adapter; share a helper
only after two maintained callers demonstrate the same contract. FIR's
existing profile receipt and package metadata already bind the necessary
inputs and outputs, so they should supply discovery and report identities
rather than another catalog.

Generated packages, samples and profiles live in ignored output directories.
Commit current recipes, source contracts and tests, and useful implementation
findings. Older artifacts and experiments can be reconstructed from Git.
Do not commit a new acceptance ledger, duplicate client corpus or fixed
millisecond gate. The external tooling CI proves that the evidence machinery
works; performance claims still require controlled representative runs.

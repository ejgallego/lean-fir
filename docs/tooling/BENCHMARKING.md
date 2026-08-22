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
  to the exact Wasm, sidecar, and workload. Its cross-run resolver folds V8
  nodes by final function identity, attributes sampled leaves to their
  immediate caller nodes, and reports per-run shares plus median, dispersion,
  and rank stability without treating profiler time as a headline benchmark.
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

## Thin roadmap

1. Capture one real `d8 --perf-prof --perf-prof-annotate-wasm` fixture before
   freezing the instruction-origin evidence schema.
2. Let each client register its representative workload and report consumer in
   the VIR catalog; FIR supplies artifact identities and profile/probe outputs.
3. Replace retained legacy raw profiles with collector-produced bound evidence
   when a client next refreshes that workload; raw profiles remain explicitly
   unbound meanwhile.
4. Use fresh client profiles to choose W7 optimization work, then route changed
   runtime contracts to W6 through the existing lane protocol.

FIR should not add a dashboard, duplicate client corpora, fixed millisecond
gates, profiler-enabled release packages, or a general benchmark framework to
complete this roadmap.

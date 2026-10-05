# FIR tooling: build, test and performance

Source review: 2026-10-05, main `8f4222cb2`, Lean 4.34.1. This page maps
maintained commands and identifies gaps; it is not a benchmark result or a
package acceptance ledger. Exact package inventories stay in BUILD.json,
and case inventories stay in their existing registries.

## Build

Lake owns Lean dependencies and native executable compilation. The root
Makefile selects the toolchain-scoped artifact cache and provides concise
commands. `make build` builds the default FIR library; it does not build
every executable, proof project or consumer package.

There are two maintained Wasm paths from final impure LCNF:

- FIR symbolic lowering plus the resident Wasm runtime, used by the
  concrete semantics/proof work and self-contained packages.
- Lean's direct C emitter plus LLVM/Emscripten, used by an independent
  executable backend with the matching upstream Lean runtime.

These have distinct ABIs and loaders. Their source capture, module setup and
runtime selection are part of the build identity, not interchangeable options
on one package. See [the generation guide](../wasm-artifact-generation.md).

The build already has useful shared pieces: toolchain-matched caches,
identity-checked Talos source mirroring, strict source preparation,
immutable publication and checksum-verified package installation.
`fir-prettyM-artifact` is a compiled frontend/emitter executable with explicit
module and entry arguments. The artifact gate builds its generators at one
barrier and then invokes them directly. Source preparation validates supplied
dependencies and original module setups; it does not itself compile a package.

The weak point is the public path from a client's source entry to a package.
Recipe-specific shell, Lean and JavaScript drivers still own substantial
orchestration, and documentation mixes current commands with migration reports.
The current recipe index lists only the two qualified prettyM packages;
other integration directories require owner qualification on current main.
Their presence alone is not build support.

The next build improvement should make each maintained recipe easy to find
and run: one documented acceptance command, explicit source/dependency inputs,
and one verified package result. Reuse existing source/package helpers when
that removes duplication. A new registry or general build framework is not
needed. [build-examples.md](../build-examples.md) remains the navigation index.

## Test

| Command | What it checks | Hosted coverage in committed workflows |
| --- | --- | --- |
| `make check` | Library/examples, scalar Wasm, native/LCNF/V8 triangle, direct-LCNF machine cases, coverage, bugs, source trust and tooling units | Core CI |
| `make talos-setup && make talos-check` | Authenticated overlay, full FirTalos cone and direct compiled trust inventories | Core Talos CI |
| `make retained-initializer-check` | Real pinned consumer capture/readback and retained initializer proof contracts | Core Talos CI |
| `make tooling-check` | Supported Node runtime, tooling units, real Binaryen indexing, live inspector profiles and compiled Array ownership probe | No workflow invokes the complete command |
| `bash integration/talos/artifact/check.sh` | Deterministic W7 production, resident helpers, package utilities/smoke and concrete engine checks | Path-triggered artifact CI |
| `bash integration/lcnf-c-wasm/check-all.sh` | Freestanding, Emscripten and WASI backend fixtures | Path-triggered C/Wasm CI |

This separation is useful. Source-generated cases and handwritten final-LCNF
machine cases answer different questions; Talos proofs and executable engine
tests complement each other. The coverage index preserves those distinctions.
The V8 matrix supplies verified native/LCNF evidence to avoid repeated
execution. Bounded native subprocess parallelism preserves case order and
keeps shared Lake and publication state serial. Failed child statuses are
propagated, and successful validation scratch is disposable.

The immediate coverage gap is the external tooling gate: pure parser tests
cannot establish that a live inspector capture, Binaryen transformation or
compiled Array probe still works. The provider-neutral Node 22/24 contract
exists, but its hosted matrix is not wired. Browser checks are another explicit
boundary: the artifact script runs them only with `FIR_BROWSER` and exhaustive
prettyM checkpoints, and committed workflows do not set that browser option.
Consumer browser campaigns therefore remain separate acceptance evidence.

Workflow path filters also still name `lakefile.lean`, whereas this checkout's
root configuration is `lakefile.toml`. Both the C and artifact workflows need
the actual file in their dependency triggers. Core CI still runs, but it does
not replace the omitted specialized gates.

The validation harness and its primary test module each exceed 10,000 lines,
and the validation guide exceeds 2,000. This is a maintenance cost, not evidence
that checks should be dropped. Future changes should preserve backend/receipt
boundaries and extract a coherent component only when normal work requires it.
Prioritize uncovered executable paths before reorganizing the harness.

## Performance

FIR's performance tooling has a clear, useful scope: explain the emitted
artifact and its runtime mechanisms. Client repositories own representative
inputs and semantic oracles; VIR owns shared browser comparison campaigns.

The maintained tooling supports:

- Final optimized function identities, hashed sidecars and bounded function
  views, including multiple link inputs and name-preserving companions.
- Checked steady Node/V8 CPU profiles bound to exact Wasm, sidecar, workload,
  inputs and dependencies; comparable multi-run aggregation with sampled callers.
- A compiled Array probe that distinguishes reads, allocation, unique updates
  and shared copy-on-write, with exact ownership/frontier ratchets.
- Instruction-origin companions and a documented real `d8`/perf consumer.
  Node's instruction source-map limitation is documented; this deeper path
  remains a diagnostic workflow rather than a routine headline benchmark.

The strength is identity and attribution: reports reject mismatched artifacts
and retain unknown functions explicitly. The main weakness is operational
consistency. Representative timing and phase collection still vary by recipe,
and no new 4.34.1 throughput campaign was run for this review. The
[throughput guide](CHECK_THROUGHPUT.md) now describes the maintained mechanisms
and measurement procedure; older 4.33 timing results and the removed Talos
attestation experiment remain retrievable in Git history.

Future performance work should start with one client-visible workload and
the public build/runtime boundary being investigated. Keep project, encode,
execute, decode, rewind and total measurements explicit. Use fresh instances
or report arena growth. Compare ordinary runs in balanced order with warmups
excluded; collect profiles separately and retain raw samples with identities.
Neither sampled shares nor the Array microprobe establish an application
speedup. See [BENCHMARKING.md](BENCHMARKING.md) for the existing contract.

## Retirement and next steps

The old 4.33 setup/attestation scripts are already removed. The former RC2
branch instructions have been replaced by current 4.34.1 commands in
[the toolchain guide](../toolchain-4.34-lane.md).

The obsolete `.github/workflows/lean-434-compat.yml`, which required RC2,
has been removed under root's narrow lease. The remaining candidate is the
three standalone 4.33 metadata files under `integration/talos`. Searches of
tracked setup, trust and CI code find the active proof route using
`tooling/talos-434` metadata instead. Their deletion still requires the
existing W6 ownership confirmation. Proof sources and the active overlay are
maintained inputs, not retirement candidates.

Recommended order after that bounded retirement:

1. Wire the external tooling gate and correct specialized CI dependency paths.
2. Qualify consumer recipes through their owners on current main; repair or
   remove obsolete recipe inputs and keep the existing index accurate.
3. Refresh build/check timing only when it answers a concrete priority question;
   otherwise use representative client profiles to select runtime work.

Keep current source recipes in Git, generated results under ignored build
directories, and checksums/provenance in each package. Git history supplies
older implementations; an old package pointer is not a current acceptance gate.

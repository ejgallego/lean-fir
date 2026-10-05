# FIR tooling: build, test and performance workflow

This page connects maintained commands, Lean 4.34.1 build inputs and the
remaining consolidation work. Exact package inventories stay in BUILD.json,
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
| `make tooling-check` | Supported Node runtime, tooling units, real Lake source preparation, Binaryen indexing, live inspector profiles and compiled Array ownership probe | Sequential Node 22/24 passes in artifact CI |
| `bash integration/talos/artifact/check.sh` | Deterministic W7 production, resident helpers, package utilities/smoke and concrete engine checks | Path-triggered artifact CI |
| `bash integration/lcnf-c-wasm/check-all.sh` | Freestanding, Emscripten and WASI backend fixtures | Path-triggered C/Wasm CI |

This separation is useful. Source-generated cases and handwritten final-LCNF
machine cases answer different questions; Talos proofs and executable engine
tests complement each other. The coverage index preserves those distinctions.
The V8 matrix supplies verified native/LCNF evidence to avoid repeated
execution. Bounded native subprocess parallelism preserves case order and
keeps shared Lake and publication state serial. Failed child statuses are
propagated, and successful validation scratch is disposable.

The artifact workflow now runs the external tooling gate on both supported
Node majors, using the same pinned tools before artifact acceptance. This
exercises live inspector capture, Binaryen identity and compiled Array
ownership rather than relying only on parser tests. Browser checks remain a
separate boundary: the artifact script runs them only with `FIR_BROWSER` and
exhaustive prettyM checkpoints, and committed workflows do not set that browser
option. Consumer browser campaigns therefore remain separate evidence.

`make -C tooling source-prepare-check` also runs the installed-Lake smoke
independently. It selects Lean through Elan from the FIR root, checks the
version against the current root pin, and derives the exact compiler commit
from that binary. No compiler/workspace arguments, historical source replay,
toolchain installation or pin override are supported by this smoke. It prepares
a current generated fixture with a supplied Git dependency whose remote is
unreachable, using the normal source-preservation and setup-identity checks.
Private inputs, setup outputs and failure logs stay in worktree-local `.deps`.
This tests preparation, not a consumer package or source-entry compilation.

Specialized workflow filters select the actual root `lakefile.toml` and
top-level Lean drivers. Artifact triggers also include tooling, the root
Makefile and its quiet/cache helpers. Core CI still runs independently.

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
has been removed under root's narrow lease. The three standalone 4.33
metadata files under `integration/talos` have also been removed after W6
confirmed the boundary and root released the hold. Tracked setup, trust and
CI code use `tooling/talos-434` metadata for the active proof route. Proof
sources, trust tests (including their synthetic old-project fixture), the
current workflows and the active overlay are preserved.

The next consolidation work is:

1. Qualify consumer recipes through their owners on current main, using the
   [client build workflow](../build-examples.md#building-a-package) below the
   existing index; repair or remove obsolete inputs.
2. Use the [performance workflow](BENCHMARKING.md#measurement-workflow) for
   comparable client measurements and exact-artifact attribution.
3. Factor a repeated preparation or timing implementation only after locating
   it in two maintained recipes and specifying the inputs, invalidation and
   semantic endpoint that a shared helper must preserve. Refresh throughput
   timing when it answers a concrete build priority.

Keep current source recipes in Git, generated results under ignored build
directories, and checksums/provenance in each package. Git history supplies
older implementations; an old package pointer is not a current acceptance gate.

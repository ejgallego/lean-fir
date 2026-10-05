# FIR external tooling CI contract

FIR defines one provider-neutral external tooling command:

```sh
make tooling-check
```

The command is intentionally separate from ordinary `make check`. It exercises
the tooling against real external programs and a compiled ordinary-Lean probe;
it is not a hosted-runner performance benchmark.

The [Wasm artifact workflow](../../.github/workflows/wasm-artifact.yml) runs
this complete command sequentially on Node 22 and 24 in its existing job,
reusing one pinned Binaryen setup. Node 24 then runs the artifact gate.
The core workflow also runs the tooling unit tier through `make check`.
See the [build/test/performance guide](BUILD_TEST_PERF.md) for the command map.

## Runtime matrix

Run the gate on Node 22 and Node 24, with Node 24 as the baseline runtime.
Both are LTS release lines as of 2026-08-22. Current non-LTS and end-of-life
Node lines are outside the contract. `tooling/ci-contract.mjs` checks the active
major and fails before the external tests when the runtime is unsupported.

This policy follows Node's production guidance and release table:
<https://nodejs.org/en/about/previous-releases>.

The gate itself does not install dependencies. Before invoking it, the runner
must provide:

- the repository's `lean-toolchain` through Elan;
- Emscripten 5.0.3's `upstream/bin` directory, normally at
  `.deps/lcnf-c-wasm/emsdk/upstream/bin`; and
- `wasm-as`, `wasm-opt`, `wasm-merge` and `wasm-metadce` from that directory.
  The Makefile authenticates the assembler/optimizer revision; the multi-input
  identity tests also execute merge and metadce from the same pinned installation.

Set `FIR_BINARYEN_DIR` when the pinned tools live elsewhere. The existing
`integration/lcnf-c-wasm/setup-emscripten.sh` can provision the repository-local
toolchain, although a CI provider may restore the same content-addressed setup
from its own cache. Provisioning may access the network; `make tooling-check`
may not.

## Required behavior

Each runtime pass consists of dependency provisioning followed by:

```sh
FIR_BINARYEN_DIR=/absolute/path/to/emscripten-5.0.3/upstream/bin \
  make tooling-check
```

The command fails closed when Node is outside the supported matrix, either
Binaryen executable is absent or has the wrong revision, a test is skipped, or
any check fails. It covers:

1. dependency-free tooling unit tests;
2. final optimized-Wasm function indexing and bounded views through pinned
   Binaryen;
3. a live same-process Node inspector profile plus exact aggregate/caller
   attribution; and
4. compilation and execution of the ordinary-Lean Array ownership probe,
   including its final-function sidecar.

The gate must not set duration thresholds, run profilers around headline timing
rounds, or substitute client benchmark corpora. Production performance and
browser campaigns remain in the client/VIR benchmark catalog; this job checks
that FIR's evidence-producing machinery is executable and internally
consistent.

## Workflow dependencies

Both specialized workflows include the actual root `lakefile.toml` and
top-level `Fir*.lean` drivers, as well as `Fir/**`, the compiler pin and manifest.
The artifact workflow additionally watches the root Makefile, `tooling/**`,
the quiet/cache helpers, shared package tools, Talos and Emscripten setup inputs.
Changes to profiling, source preparation or the Array probe therefore trigger
the live tooling gate rather than only its unit tests. The existing core CI
continues to run independently.

Workflow wiring is source configuration; successful local passes are not a
hosted-run claim. Root reviews/lands the exact checkpoint, and GitHub run logs
provide the hosted validation record after authorized publication.

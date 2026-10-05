# FIR check throughput

The maintained throughput mechanisms are part of the ordinary check graph.
Timing results from earlier Lean 4.33 experiments are available in Git history;
they are not current 4.34.1 latency claims or inputs to the checks.

## Current mechanisms

The root coverage graph executes the native/LCNF/V8 matrix once. Its
native/LCNF comparison also supplies the source tier, after
`scripts/verify_validation_reuse.py` verifies the selected corpus, requested
comparison pairs and current input/tool/build identities. `make validate`
remains available as an independent two-backend diagnostic.

The artifact gate verifies a current V8 receipt and regenerates the matrix
when that receipt is absent or stale. Receipts are scratch for the current
run; `make check` refreshes validation output before starting and cleans it
after success. Set `FIR_KEEP_VALIDATION=1` only for a specific investigation.
An artifact check run after that cleanup must regenerate missing evidence.

Native per-case subprocesses use `FIR_CHECK_JOBS` (root default: eight).
Their outputs are disjoint and coordinator results retain selected-case order.
LCNF, V8, shared Lake state, receipt aggregation and publication stay serial.
Invalid bounds and failed workers fail the gate.

The artifact script builds its two generator executables at one barrier,
then invokes those binaries directly. With explicit parallelism enabled,
narrow pairs of independent producers use disjoint files/roots; both statuses
must succeed before comparison or publication. Direct artifact-script use
defaults to one worker.

Talos gates now always use the authenticated 4.34.1 overlay and current
compiled trust audit. The old standalone Talos setup and build-attestation
utility have been removed. There is no persistent Talos acceptance receipt
or attestation-based bypass of the current gate.

## Measuring another change

Start with the documented commands and keep their boundaries separate:

```sh
mkdir -p .deps/tmp
TMPDIR="$PWD/.deps/tmp" /usr/bin/time -v make check
TMPDIR="$PWD/.deps/tmp" /usr/bin/time -v make talos-check
TMPDIR="$PWD/.deps/tmp" /usr/bin/time -v bash integration/talos/artifact/check.sh
```

Provision dependencies before warm measurements. Record exact source/compiler
identities, cache state, worker bounds, command order, wall/user/system time,
peak RSS and gate results. Public-command wall time includes Lake planning,
restoration, compilation, execution and verification actually performed by
that command. A direct binary sample has a narrower boundary.

For a proposed change, rotate baseline/candidate order, exclude warmups,
retain raw runs under ignored worktree-local `.deps`, and report median,
dispersion and paired deltas. Keep profilers out of headline runs. First
attribute expensive phases using Lake jobs and frontend evidence; use native
or Wasm sampling when execution accounts for the cost.

Preserve selected case inventories, comparison edges, current identity checks,
deterministic artifacts and publication ordering. A speedup cannot come from
skipping these obligations. CI logs record correctness; hosted-runner elapsed
time is not a controlled performance comparison.

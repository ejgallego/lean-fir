# FIR check-throughput measurements

This report tracks measured changes to FIR's local integration gates. The goal
is lower warm wall time without changing the cases, observations, retained
evidence, deterministic artifacts, or fail-closed behavior.

Large raw logs and GNU `time -v` records stay in the ignored worktree-local
directory `.deps/check-throughput/`. They are not a portable benchmark corpus
and are not committed.

## Serial baseline

The baseline is exact clean FIR commit
`777c4ec4fae8f4940559cba75eb184480d9943b9`, Lean 4.33.0 commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`, Node 24.19.0, and Linux x86-64
7.2.0 on a host exposing 24 logical CPUs. Talos is pinned at
`0e05edbcfbb105b33e90c60b4f50e2cf193d9254`; the artifact gate uses the
worktree-local Emscripten 5.0.3 installation.

Provisioning, dependency download, artifact-cache restoration, the first
Lean/C build, and the first Emscripten system-library population were completed
before measurement. One complete unmeasured warm-up then preceded three serial
measured rounds. Each round ran, in order:

1. `make check`;
2. `make talos-check`; and
3. `bash integration/talos/artifact/check.sh`.

No profiler ran during measurement. GNU `time -v` captured wall, user, system,
maximum RSS, I/O, and scheduler counters for each phase. Command output and the
nine raw timing records are under `.deps/check-throughput/baseline/`.

| Phase | Warm wall samples (s) | Median (s) | MAD (s) | CPU utilization samples | Median effective cores |
| --- | --- | ---: | ---: | --- | ---: |
| `make check` | 118.44, 139.84, 131.76 | 131.76 | 8.08 | 95%, 90%, 95% | 0.95 |
| `make talos-check` | 2.02, 1.38, 1.74 | 1.74 | 0.36 | 126%, 127%, 129% | 1.27 |
| artifact gate | 110.42, 97.31, 105.70 | 105.70 | 4.72 | 93%, 91%, 95% | 0.93 |
| complete ordered sequence | 230.88, 238.53, 239.20 | 238.53 | 0.67 | 94.9%, 90.9%, 95.7% | 0.95 |

The baseline therefore spends about four warm minutes while averaging less
than one of the host's 24 logical CPUs. The two largest directly observed
duplications are:

- `make check` executes the 721-case native/LCNF pair, then executes native and
  LCNF again as part of the 721-case native/LCNF/V8 matrix; and
- the artifact gate invokes that complete V8 matrix again before checking its
  concrete products.

The artifact script also repeatedly enters Lake after its build, performs a
Talos differential build already covered by the preceding exact-head Talos
gate, and generates two deterministic artifact roots serially. Those are
secondary slices: duplicate semantic execution is removed first, then one
explicit build barrier is introduced, and only then is bounded concurrency
considered.

## Evidence invariants

Every candidate must retain the same selected case inventories and comparison
edges, verify immutable validation evidence rather than trusting path
existence, reject stale build/tool/input identities, preserve deterministic
Wasm and package checksums, and leave publication and pointer replacement
serial. A lower wall time is not accepted if any of these checks is weakened.

## Duplicate native/LCNF execution

The first candidate lets the complete V8 matrix satisfy the source-native/LCNF
coverage tier. The matrix already executes each backend once, and its retained
`native--lcnf` comparison and LCNF machine-coverage artifacts are byte-identical
to the standalone pair's artifacts at the baseline checkpoint.

Reuse is not inferred from a pathname. `scripts/verify_validation_reuse.py`
verifies the immutable receipt, re-hashes every current retained plan/config,
tool, and build input, reconstructs the current native corpus through the
already-built oracle, requires exact selected-case equality for the requested
plan, and requires every requested comparison pair to be present. Unknown
binding kinds, external paths without an explicit resolver, changed files,
missing cases, and missing pairs fail closed.

`make validate` remains the standalone two-backend command. The root coverage
graph uses the verified V8 superset and therefore does not execute native and
LCNF twice.

Three warm candidate `make check` samples were 94.98, 88.19, and 88.25
seconds: median 88.25 seconds, MAD 0.06 seconds, and median utilization 0.94
effective cores. Against the serial baseline median of 131.76 seconds, this is
a 43.51-second or 33.0% wall-time reduction. Median user-plus-system CPU time
fell from 125.57 to 83.63 seconds. The accepted attribution is the eliminated
standalone native/LCNF execution minus the small cost of re-hashing current
receipt bindings; no concurrency is active in this candidate.

All three candidate rounds retained 730 unique cases, 2,172/2,172 equal
comparisons, zero findings, and native-oracle attestation contract
`3bdb36b133adfb49bbe6e0fcd697f15a5264636d5d45f87dddb4fe542ece5ab1`.
The baseline standalone and candidate superset matrices have byte-identical
native/LCNF comparison SHA-256
`d8be816dcaec16d2727d792807a4796edf50f881ad463e3116e99db0e5f2cd5c`
and LCNF coverage SHA-256
`278ef6698278fe48e70b94b05496ade4c5d595d157f82585d930d378fa912f14`.

The artifact gate consumes the same verifier in an opt-in ensure mode. An
exact current V8 receipt is reused; a missing or mismatched receipt triggers a
full `make validate-v8` and a second verification. If the regenerated receipt
still does not bind the current inputs, tools, build identities, corpus, case
selection, and all three comparison pairs, the artifact gate fails. Unit tests
cover the reuse, rerun-and-accept, and rerun-then-reject paths.

Three warm complete artifact-gate samples with an exact reusable receipt were
46.71, 45.65, and 45.95 seconds: median 45.95 seconds, MAD 0.30 seconds,
and median utilization 0.98 effective cores. Against the serial baseline
median of 105.70 seconds, this is a 59.75-second or 56.5% wall-time reduction.
Median user-plus-system CPU time fell from 101.20 to 45.48 seconds. Every
round verified 721 cases and all three requested pairs before reuse, retained
the 658 executable / 63 ByteArray-blocked concrete validation inventory,
passed all deterministic first/second artifact comparisons, and reported
44/44 concrete-readiness artifacts and 16/16 sources. No parallelism is active
in this candidate; the accepted attribution is removal of the artifact gate's
third full V8-matrix execution.

## Artifact generator build barrier

The next candidate names both artifact-generator executables in one explicit
Lake build barrier. After the barrier, 71 identical `lake exe` entries invoke
the already-built executables directly. Dynamic Lean source generation and the
Talos-owned differential/oracle paths remain unchanged. The script fails
before generation if either expected executable is absent or not executable.

Focused direct-invocation probes produced byte-identical resident-global and
Float-source Wasm artifacts. Three warm complete artifact-gate samples were
35.77, 42.28, and 33.99 seconds: median 35.77 seconds, MAD 1.78 seconds, and
median utilization 1.08 effective cores. This is 10.18 seconds or 22.2% below
the exact-receipt candidate median, and 69.93 seconds or 66.2% below the
original artifact baseline. Median user-plus-system CPU time fell from 45.48
to 38.93 seconds relative to the exact-receipt candidate.

All three rounds verified the exact 721-case, three-pair receipt, retained the
658 executable / 63 ByteArray-blocked concrete validation inventory, passed
the deterministic first/second artifact comparisons, and reported 44/44
concrete-readiness artifacts and 16/16 sources. This candidate adds no
parallelism and does not skip the incremental Talos build; exact-checkpoint
Talos attestation is a later isolated slice.

## Exact Talos build reuse

`make talos-check` now records a canonical, atomic, ignored receipt only after
the complete Talos build succeeds. The receipt binds the Git head, FIR/Talos/
interpreter Lean sources and manifests, the attestation implementation, the
Lean and Lake executables, and the `FirTalos.Differential` OLean/ILean/hash/
trace output set. Symlinks, noncanonical receipts, missing outputs, and any
content or head drift reject reuse.

The artifact gate verifies this receipt before its incremental differential
build. Exact evidence skips that repeated build. Missing or stale evidence
retains the previous behavior and rebuilds `FirTalos.Differential`; a complete
fallback artifact run exercised that path successfully. The fallback does not
write a full-build receipt because it did not execute the full Talos gate.

Three warm attested artifact-gate samples were 31.21, 31.49, and 30.55
seconds: median 31.21 seconds, MAD 0.28 seconds, and median utilization 1.14
effective cores. This is 4.56 seconds or 12.7% below the build-barrier
candidate median and 74.49 seconds or 70.5% below the original artifact
baseline. Median user-plus-system CPU time fell from 38.93 to 35.53 seconds
relative to the build-barrier candidate. All three rounds retained the exact
validation, deterministic-artifact, and 44/44 readiness inventories.

## Bounded native validation

The root Makefile sets `FIR_CHECK_JOBS=8` by default; direct script consumers
remain serial unless they opt in. The validation harness accepts only bounds
from 1 through 64 and uses the pool solely for native and direct-native
per-case executables. These processes do not write Lake state and already own
disjoint case/backend output directories. LCNF, V8, product-provider, matrix,
receipt, attestation, checksum, and publication phases remain serial.

Workers return results to the coordinator in selected-case order, so canonical
result and artifact inventories do not depend on completion order. An
exception cancels queued work and propagates before matrix/receipt publication.
Focused tests exercise the worker bound, out-of-order completion, invalid job
counts, and failure propagation.

A six-case mixed serial/eight-worker probe retained identical comparison and
LCNF coverage bytes. FIR's evidence comparator classified the complete
evidence as portable-equivalent: same run identity, semantic results, coverage,
telemetry, findings, receipts, and comparisons. Exact evidence differed only
in raw LCNF panic backtrace addresses, an existing ASLR-dependent artifact
that also varies between serial runs.

Three warm eight-worker `make check` samples were 60.52, 63.51, and 61.21
seconds: median 61.21 seconds, MAD 0.69 seconds, and median utilization 1.34
effective cores. This is 27.04 seconds or 30.6% below the serial deduplicated
candidate median and 70.55 seconds or 53.5% below the original root-check
baseline. Median user-plus-system CPU time was 85.53 seconds versus 83.63 for
the serial deduplicated candidate. Every round retained 730 unique cases,
2,172/2,172 equal comparisons, zero findings, and the same native-oracle
contract. Two full parallel evidence snapshots were independently verified as
portable-equivalent. A final explicit `FIR_CHECK_JOBS=1 make check` compatibility
run passed the same 730-case / 2,172-comparison gate in 90.02 seconds.

## Bounded deterministic artifact production

The artifact gate uses the same job bound for two narrowly independent pairs.
Direct script use remains serial by default. With `FIR_CHECK_JOBS` greater than
one, the first and second Float source artifacts are generated and executed in
different filenames, and the first and second concrete artifact inventories
are generated in different temporary roots. There are exactly two producers
in either region. Lake builds, Lean oracle creation, byte comparisons,
readiness aggregation, browser checks, checksums, and publication remain
serial.

The pair runner waits for both processes, records both statuses, and fails if
either producer fails. Focused tests cover serial order, parallel completion,
and failure propagation in both modes. An invalid bound fails before artifact
work begins.

Seven order-balanced ignored-only rounds of the complete `all` plus 19
resident-artifact inventory measured serial wall samples of 2.79, 2.68, 2.74,
2.71, 2.72, 2.81, and 3.04 seconds: median 2.74 and MAD 0.05. The two-root
parallel samples were 1.41, 1.82, 1.35, 1.34, 1.30, 1.34, and 1.60 seconds:
median 1.35 and MAD 0.05. All four roots in every round contained the same 126
byte-identical files. This removes 1.39 seconds, or 50.7%, from that region.

Seven order-balanced Float-source rounds measured serial wall samples of 3.87,
3.73, 3.87, 3.72, 3.81, 3.83, and 4.10 seconds: median 3.83 and MAD 0.04. The
parallel samples were 1.99, 2.00, 2.00, 1.99, 1.91, 2.11, and 2.47 seconds:
median 2.00 and MAD 0.01. Every `.wasm`, manifest, final LCNF, function
inventory, and oracle sidecar was byte-identical. This removes 1.83 seconds,
or 47.8%, from that region. Together the two isolated regions remove 3.22
seconds of measured serial critical-path work.

Three complete parallel artifact gates passed in 29.33, 32.49, and 34.09
seconds (median 32.49, MAD 1.60), including exact validation and Talos receipt
reuse, deterministic comparisons, 44/44 readiness artifacts, and 16/16
sources. These whole-gate samples were taken while other repository work was
active and are noisier than the bounded phase measurements, so no additional
whole-gate percentage claim is made. A complete explicit `FIR_CHECK_JOBS=1`
fallback gate also passed; its 49.37-second wall time was visibly contaminated
by concurrent host load and is retained as correctness evidence only.

## Isolated source-artifact determinism

Ordinary source generation elaborates fixture files that contain embedded
`#fir_wasm_emit` commands. Even when the requested output paths differ, those
commands write another 54 products to a relative `_build` directory. The gate
therefore does not launch two source generators from the repository root.
Instead, each producer receives a private working directory and private output
root under the gate's existing temporary roots. Both use the same read-only
Lake environment after the build barrier.

Each producer emits 63 files: the 54 elaboration products plus the selected
prettyM and PrettyTrace Wasm, manifests, final LCNF, instruction origins,
function inventory, and final function sidecar. The gate compares the complete
private directory trees serially and promotes one verified tree into canonical
`_build` only after they agree. A producer failure or mismatch occurs before
that promotion and before package publication. Exhaustive pretty/browser mode
retains its existing serial source-generation path.

Seven order-balanced ignored-only rounds measured serial source-tree samples
of 11.89, 10.81, 11.32, 12.55, 10.96, 10.86, and 10.82 seconds: median 10.96
and MAD 0.15. Parallel samples were 6.14, 5.58, 5.61, 6.42, 4.89, 5.58, and
5.68 seconds: median 5.61 and MAD 0.07. Every serial and parallel tree was
byte-identical in every round. This removes 5.35 seconds, or 48.8%, from the
source-production region.

Three contemporaneous complete-gate rounds measured serial samples of 31.14,
30.20, and 30.84 seconds (median 30.84, MAD 0.30) and bounded samples of 26.51,
22.33, and 22.99 seconds (median 22.99, MAD 0.66). This is a 7.85-second or
25.5% end-to-end reduction for the cumulative Float, direct/resident, and
source-artifact pairs. Every run retained exact validation and Talos receipt
reuse, all deterministic comparisons, 44/44 readiness artifacts, and 16/16
sources.

The exhaustive path currently fails in the unchanged
`FirWasmSourceExample.lean` resident-getTag checkpoint with
`memoryInstructionWithoutMemory`. Running the parent checkpoint's exact script
under the same exhaustive environment reproduces the failure before this
slice's isolation path is entered. It is reported as a separate W7 follow-up,
not worked around by tooling.

## Isolated oracle production

The two live FIR oracle runs read the same built Lean modules but write
expected observations into different artifact roots. Each run now also owns a
private `TMPDIR`; `lake env` only supplies the read-only package environment,
while `lean --run` places its transient compiler files in that private root.
The same bounded pair helper waits for both statuses. All Wasm/manifest/oracle
comparisons and readiness checks remain serial, and direct script use remains
serial by default.

Seven order-balanced rounds measured serial samples of 2.68, 2.22, 2.53, 3.12,
2.55, 2.43, and 2.46 seconds: median 2.53 and MAD 0.10. Parallel samples were
1.33, 1.21, 1.45, 1.53, 1.25, 1.32, and 1.56 seconds: median 1.33 and MAD
0.12. All four 44-observation roots in every round were byte-identical. This
removes 1.20 seconds, or 47.4%, from the oracle-production region without a
concurrent Lake build or shared output path.

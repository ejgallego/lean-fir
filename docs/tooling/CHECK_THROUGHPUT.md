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

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

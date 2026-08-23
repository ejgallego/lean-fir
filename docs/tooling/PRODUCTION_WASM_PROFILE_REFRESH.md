# Production Wasm profile refresh

Status: checked diagnostic evidence collected on 2026-08-22 from the accepted
FIR `ee1f3e2d` prettyM and lean-zip packages. This refresh replaces unbound or
legacy-schema profiles for current prioritization. It does not retroactively
make the historical controls in
[`WASM_CALLER_ATTRIBUTION.md`](WASM_CALLER_ATTRIBUTION.md) comparable with the
new artifacts.

## Evidence boundary

The raw evidence is intentionally ignored under the tooling worktree at
`.deps/evidence-refresh/`. `SHA256SUMS` binds the complete retained inventory;
its SHA-256 is
`19fcb87d0f723771e6c55eacea521f5ea804adfc35903533ed1ebb31d06bb61e`.
That inventory contains four untouched V8 CPU profiles and four
`fir.sampled-profile/v2` reports for each workload, the two
`fir.sampled-profile-aggregate/v3` reports, workload receipts, and the one
FIR-local prettyM workload driver/input.

The collector ran on Node `v24.19.0`, V8 `13.6.233.17-node.51`, Linux x64,
with a 500-microsecond requested sampling interval. Every run uses a fresh
Wasm instance. All eight captures are `checked-diagnostic`; both aggregates
are `comparable-diagnostic`, all samples resolve through their exact final
function sidecars, and neither aggregate has a comparability limitation.

The package-local prettyM and lean-zip smokes passed immediately before the
captures. The immutable package identities are:

| Workload | Source | Wasm | Final function sidecar | Imports |
| --- | --- | --- | --- | ---: |
| prettyM | FIR `ee1f3e2d910d915155b805f1081c2bf67fc28bfc` | 88,197 bytes; `efdb6672...fb2a` | 126,158 bytes; `250f239a...594` | 0 |
| lean-zip raw | FIR `ee1f3e2d910d915155b805f1081c2bf67fc28bfc`; lean-zip `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21` | 393,070 bytes; `3b4288d2...85c` | 210,354 bytes; `519140cf...21e`; 508 functions | 0 |

The prettyM aggregate is 411,028 bytes with SHA-256 `2df276aa...3d78`.
The lean-zip aggregate is 701,630 bytes with SHA-256 `03c9e1d8...5c0e`.
The complete hashes remain in the ignored checksum inventory.

## Workload contracts

The prettyM workload is the historical grouped-document stress shape: 256
break opportunities, 1,026 `Std.Format` nodes, width 16, one checked first
call, three warmups, 256 inputs prepared before profiling, 256 profiled Wasm
entry calls, and two complete `PrettyTrace` decodes. The first, warm, first
profiled, and last profiled results agree on:

- 513 UTF-8 output bytes, SHA-256 `ba9f4575...25b`;
- 1,026 styling events, SHA-256 `4f1eedf4...c36`.

The ignored driver constructs only the profiling fixture; it does not create
a competing benchmark catalog. The canonical browser workload remains owned
by VIR.

The lean-zip workload reuses the client-owned
`bench/fir-native/profile-workload.mjs` at lean-zip `4f72e48b`. It exercises a
deterministic 256-KiB seeded-random input at level 6, with one checked and
independently inflated first call, three warmups, and sixteen profiled calls.
Every output is 262,169 bytes with SHA-256 `fe8182f2...f75e`; the persistent
frontier and cache-aware rewind observations agree across all four instances.

## Capture quality

Steady elapsed values below delimit the sampled windows. They are diagnostics
for profile quality, not headline performance measurements.

| Workload | Run | Steady window | Wasm self samples | Host samples |
| --- | ---: | ---: | ---: | ---: |
| prettyM | 1 | 221.23 ms | 285 | 104 |
| prettyM | 2 | 277.81 ms | 393 | 100 |
| prettyM | 3 | 146.72 ms | 212 | 53 |
| prettyM | 4 | 170.90 ms | 237 | 71 |
| lean-zip | 1 | 2920.47 ms | 5,179 | 28 |
| lean-zip | 2 | 1705.09 ms | 3,049 | 19 |
| lean-zip | 3 | 1596.14 ms | 2,855 | 16 |
| lean-zip | 4 | 2439.64 ms | 4,330 | 25 |

All runs exceed the 100-Wasm-sample quality floor. Exact phase-overlap
`timeDeltas`, rather than a uniform-profile approximation, select the steady
window.

## Current attribution

prettyM is dominated by resident allocation. Across the four runs the
allocation family accounts for 89--153 self samples, or 38.0--46.3% of Wasm
self samples. Reference counting accounts for 16.1--18.3%, and retained Lean
source functions account for 12.7--15.1%.

The stable leading individual functions are:

| Function | Median Wasm-self share | MAD | Median rank |
| --- | ---: | ---: | ---: |
| `fir_alloc_ctor_10` | 14.05% | 1.12% | 1 |
| specialized `Std.Format.be`/`prettyM` worker | 9.97% | 1.31% | 2 |
| `fir_alloc_ctor_17` | 8.10% | 0.95% | 3 |
| `fir_dec_once` | 6.85% | 0.56% | 4 |
| `fir_alloc_ctor_9` | 5.78% | 0.41% | 5.5 |

This makes constructor allocation consolidation a stronger current prettyM
probe than a narrow release-only change. Reference counting is still material,
but it is not the leading family.

lean-zip has a broader split. Retained Lean source functions account for
42.0--54.9% of self samples; numeric helpers 19.8--25.9%; reference counting
12.6--17.3%; and Array/ByteArray helpers 12.0--15.3%.

| Function | Median Wasm-self share | MAD | Median rank |
| --- | ---: | ---: | ---: |
| `Zip.Native.Deflate.lzMatchP` | 30.32% | 4.48% | 1 |
| `fir_dec_once` | 14.50% | 1.61% | 2 |
| `Zip.Native.Deflate.chainWalkPackedUBelow._redArg` | 6.90% | 1.02% | 3 |
| `fir_byte_array_validate` | 5.34% | 0.27% | 4 |
| `Zip.Native.Deflate.chooseSplitsHeuristicPUPacked` | 4.26% | 0.51% | 5 |
| `fir_big_ext_Nat_add` | 3.90% | 0.13% | 6 |
| `fir_ext_Array_set` | 2.85% | 0.31% | 10.5 |

The exact caller evidence sharpens the next compiler/runtime questions:

- `lzMatchP` supplies a median 46.65% of `fir_dec_once` samples;
- `lzMatchP` supplies 39.36% of `fir_byte_array_validate`, while
  `fir_ext_ByteArray_size` supplies another 28.38%;
- `lzMatchP` supplies 57.96% of `fir_big_ext_Nat_add` and 86.68% of
  `fir_ext_Array_set`.

The accepted closed-closure package has a much smaller and differently indexed
final module than the historical 2,305-function package. The caller movement
is therefore a useful fresh prioritization signal, not evidence of a speedup or
regression against the old campaign.

## Tooling assessment and refresh policy

No tooling source change was required. The existing collector, workload
receipt, exact function resolver, quality gate, aggregate statistics, and
caller attribution were sufficient for both production packages. A generic
cross-artifact comparison command remains unjustified by this slice: lean-zip
already owns its semantic comparator, and prettyM has no second eligible
current artifact in this campaign.

When W7 accepts a new package, capture it as a separate candidate with the
same workload module, receipt identities, Node/V8 version, sampling interval,
and semantic observations. Never redirect an old evidence record through a
moving `*-current` symlink. Use order-balanced, unprofiled client measurements
for elapsed claims; use these profiles only to explain final-function and
caller movement.

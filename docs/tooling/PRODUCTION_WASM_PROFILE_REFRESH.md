# Production Wasm profile refresh

Status: checked diagnostic evidence collected on 2026-08-22 from the accepted
FIR `ee1f3e2d` prettyM and lean-zip packages, followed by exact final-package
evidence for the accepted prettyM constructor work on 2026-08-25. This refresh
replaces unbound or legacy-schema profiles for current prioritization. It does
not retroactively make the historical controls in
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

## Trusted ByteArray follow-up

Lean-zip independently accepted and profiled the trusted closed-ByteArray
candidate on 2026-08-22. The client-owned evidence is retained at
`lean-zip@b22b5b11:bench/results/wasm/2026-08-22-fir-bytearray-trusted-refresh/`;
the `SHA256SUMS` file hashes to
`9b8637cc0fb53a52886b3999556ccf71d68cfe4400bfe658d4d372ab8271764d`.
FIR does not duplicate that workload, browser campaign, or raw profile corpus.

The candidate package was produced at FIR `dc35f594`, contains a 393,275-byte
zero-import Wasm module with SHA-256
`06bec0d90846f4ce40e19169346d4dbfc19a79556bb23c787241b73bce04749f`,
and binds a 208,398-byte exact-function sidecar with SHA-256
`8f3a9bd1dcf315f05c3f13acdc375de2d1968df187e47d46b608baf6a25796f1`.
Four checked v2 captures and their comparable-diagnostic v3 aggregate have no
reported limitations. `fir_byte_array_validate` is absent from both the final
sidecar and all sampled execution, closing validation as a lean-zip runtime
hotspot. The fresh leading median shares are `lzMatchP` 29.65%, `fir_dec_once`
15.92%, and `fir_ext_Array_set` 3.32%; `lzMatchP` supplies a median 52.5% of
the remaining `fir_dec_once` samples.

The client deliberately makes no cross-artifact browser timing claim because
the retained A/B/A sweeps encountered material order and host-load movement.
W7's separate order-balanced 28-sample run (35.395 ms control versus 31.506 ms
candidate) remains directional evidence only. The next exact-profile candidate
is therefore prettyM constructor allocation once W7 publishes a clean immutable
package; shared decrement, Array writes, and numeric helpers remain separate
questions rather than being attributed to this ByteArray slice.

## prettyM constructor follow-up

W7 subsequently published the clean immutable package at FIR
`cf3f7cb88506d9a282a444e5757b0e48acc296ee`. Its zero-import Wasm module is
83,996 bytes with SHA-256
`fc61301d946b1596ad08c9b20d51d2e1f68d60ca0c04b0f9d56e298c2ec6408d`;
the 126,117-byte exact-function sidecar has SHA-256
`ff31d65ff0d9daddfe96b47ef1f9116b8777c98eea26fc816e232d4871e72cd2`
and names 314 final functions. Package checksums, smoke, styled output, and the
sidecar verifier passed immediately before profiling.

The capture reused the byte-identical 4,543-byte grouped-document driver and
95-byte input from the constructor experiment. One checked first call, three
warmups, 256 prepared and profiled calls, and both styled decodes retain the
same 513-byte text SHA-256 `ba9f4575...25b` and 1,026-event SHA-256
`4f1eedf4...c36` in every phase of all four fresh instances. The raw evidence
is retained under the tooling worktree at
`.deps/experiments/pretty-constructor-final/`; its `SHA256SUMS` hashes to
`951232d4bd22b6f02fa550fdc439e4da27cbf9d9df960bc0f3154ce15dec81b3`.
The v3 aggregate itself hashes to
`2552a18af8dd70ac5a7f2b8d966f32369701113528c570d7ee8cdd899f193307`.

All four v2 captures are `checked-diagnostic`, and the aggregate is
`comparable-diagnostic` with no limitations. Node `v24.19.0`, V8
`13.6.233.17-node.51`, Linux x64, and the 500-microsecond requested sampling
interval match the earlier refresh.

| Run | Steady window | Wasm self samples | Host samples |
| ---: | ---: | ---: | ---: |
| 1 | 257.37 ms | 174 | 61 |
| 2 | 301.25 ms | 166 | 77 |
| 3 | 221.47 ms | 143 | 60 |
| 4 | 280.65 ms | 195 | 57 |

The accepted work has a deterministic size result. The first two rows below
are dirty, isolated W7 experiment source views; the final row is the clean
publication. Cross-artifact sampled shares remain diagnostic rather than a
timing comparison.

| Package | Wasm bytes | Final functions | Constructor-helper body bytes | Median allocation share |
| --- | ---: | ---: | ---: | ---: |
| exact experiment baseline `b4babe10...811` | 87,513 | 308 | 6,567 | 43.66% |
| sparse initialization `47dd699a...9c8` | 85,418 | 314 | 5,002 | 45.06% |
| clean final `fc61301d...08d` | 83,996 | 314 | 3,852 | 45.65% |

Relative to the exact experiment baseline, the final module is 3,517 bytes
(4.02%) smaller and the constructor-helper bodies are 2,715 bytes (41.3%)
smaller. Scratch-free constructor returns account for another 1,150 helper-body
bytes beyond sparse initialization. This is a clear code-size win even though
the selected closure contains six more final functions.

Allocation remains the leading sampled family in the final package: its four
runs span 37.93--52.45% with median 45.65% and MAD 5.44 percentage points.
Reference counting has median 18.78%, while retained Lean source functions have
median 14.09% with a much wider 4.58-point MAD. The leading final functions are:

| Function | Median Wasm-self share | MAD | Median rank |
| --- | ---: | ---: | ---: |
| specialized `Std.Format.be`/`prettyM` worker | 10.46% | 2.78% | 2.5 |
| `fir_alloc_ctor_10` | 10.33% | 2.96% | 3 |
| `fir_heap_alloc` | 8.96% | 0.76% | 2.5 |
| `fir_alloc_ctor_17` | 8.51% | 0.39% | 3 |
| `fir_dec_once` | 7.33% | 0.63% | 5.5 |
| `fir_alloc_ctor_9` | 6.90% | 1.58% | 5.5 |

Immediate-caller evidence keeps the sampled constructors local to the real
pretty-printer path: the specialized worker supplies a median 64.1% of
`fir_alloc_ctor_10`, 53.6% of `fir_alloc_ctor_17`, and all sampled
`fir_alloc_ctor_9`, `_12`, and `_16` self time. The optimization removed
unnecessary initialization and scratch-result code, but it does not remove the
semantic constructor allocations made by this workload. No runtime-speed claim
is warranted; a further allocation experiment should target call count,
consolidation, or representation rather than more zero-fill removal.

## Tooling assessment and refresh policy

No tooling source change was required. The existing collector, workload
receipt, exact function resolver, quality gate, aggregate statistics, and
caller attribution were sufficient for both production packages. A generic
cross-artifact comparison command remains unjustified by this slice: lean-zip
already owns its semantic comparator, and prettyM has no second eligible
current artifact in this campaign.

The final constructor package demonstrates the intended refresh protocol: each
package is captured separately with the same workload module, semantic
endpoint, Node/V8 version, sampling interval, and observations, while its
receipt binds the changed package dependencies. Never redirect an old evidence
record through a moving `*-current` symlink. Use order-balanced, unprofiled
client measurements for elapsed claims; use these profiles only to explain
final-function and caller movement.

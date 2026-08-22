# Production Wasm provenance cost

Status: measured on 2026-08-22. Instruction origins remain an opt-in,
regenerable diagnostic. They are not part of ordinary application packages or
the final-function profile schema.

## Identities and method

The W7-2 source slice `475eb50bc80c` cherry-picked without conflicts over the
then-current checked-Nat main `b3b823802998`. After the proof-only main advance,
the same slice rebased without conflicts over `345a0cb3e0dc` and landed as
`f701b8bf`. Exact emitter-final indexing then landed at `f661a080`, followed by
the prettyM sidecar and package consumer at `f74709fc`.

Measurements were collected from the first candidate, `1379b73b22bb`, before
the proof-only advance. The generated W7 files are identical in both
candidates. The host ran Lean 4.33.0 Release at
`d8b18978322de05a8f3dba51ef03cf5461676c17`, Node 24.19.0, and Linux 7.2.0
x86-64. Lake compilation completed before timing. Temporary files and raw runs
were retained under the tooling worktree's ignored `.deps` directory.

Elapsed-time evidence is noisy. Hashes, byte lengths, origin counts, successful
opcode validation, and clean Git application are deterministic evidence.

## prettyM

The representative command ran the existing `fir-prettyM-artifact` executable
on `FirWasmPrettyTraceExample.lean`. The baseline used the ordinary invocation;
the candidate added `--instruction-origins`. One warmup per command preceded
eight AB/BA measured passes. Both commands wrote separate files, exited zero,
and produced byte-identical Wasm on every run.

| Measurement | Ordinary | With origins |
| --- | ---: | ---: |
| Runs | 8 | 8 |
| Median wall time | 2,343.703 ms | 5,651.079 ms |
| Standard deviation | 231.734 ms | 543.394 ms |
| Minimum | 1,868.221 ms | 4,723.906 ms |
| Maximum | 2,569.846 ms | 6,280.310 ms |

The median paired overhead was 3,309.013 ms. Comparing the independent medians
gives 3,307.376 ms, or 141.12%. The phase reported by the generator itself had
a 3,272 ms median, 166.5 ms median absolute deviation, and 3,048--3,740 ms
range. Baseline and diagnostic frontend medians were 2,005.5 and 1,991 ms, so
the measured difference is localized to provenance generation rather than
source elaboration.

The current checked-Nat artifact identities are:

- ordinary and diagnostic Wasm: 120,739 bytes, SHA-256
  `06cb977fa8a0815c2bfd1762ff08031daa1f723221dd6054b39f32f823210119`;
- compact origin table: 605,049 bytes, SHA-256
  `770b81d42f9d7123adbbd715443f0452f2a200a7616d368ac2793017a6656031`;
- 393 defined functions and 35,615 checked symbolic instruction origins.

The compact table is 5.01 times the Wasm byte length. The existing validator
resolved every row to the recorded opcode in the ordinary module. This
supports keeping the table regenerable and out of the immutable browser
package.

## Exact-release aggregation

The landed `fir.sampled-profile-aggregate/v1` consumer accepts exact-release
final-function indices, not pre-optimization instruction tables. Joining those
schemas by position would silently misattribute inlined, deleted, reordered,
or synthesized code, so no such join was attempted.

The new prettyM `exact-emitter-final-order/v1` sidecar permits exact function-
level aggregation without such a join. Tooling independently re-derived the
four bound profiles byte-for-byte, with zero unresolved Wasm samples. The
120,739-byte Wasm retains SHA-256
`06cb977fa8a0815c2bfd1762ff08031daa1f723221dd6054b39f32f823210119`;
its 164,320-byte function sidecar has SHA-256
`569c327ae3cb986aa67ba0ac5b7f564798cfbd4b753388b26bda8bcab3b96b04`.
The reproduced aggregate has SHA-256
`8e61f6dfff831cef46fb1105dc4456818d1168a422971ce88a015fa70106b097`.

The workload performs 256 prepared executions of the grouped styled document
and two checked decodes. Every run produced the same trace digest, 3,070 text
characters, 1,025 styling events, and final frontier 124,730,520. Its leading
median shares of Wasm self time were:

| Rank | Final function | Median share | MAD |
| ---: | --- | ---: | ---: |
| 1 | `fir_dec_once` | 9.55% | 0.79 pp |
| 2 | `fir_alloc_ctor_10` | 8.72% | 0.53 pp |
| 3 | `fir_inc_0` | 4.23% | 0.41 pp |
| 4 | `Std.Format.prettyM` specialized worker | 4.13% | 0.74 pp |
| 5 | `fir_getTag` | 3.97% | 0.59 pp |

This is exact function-level attribution for the shipped bytes. It does not
turn the pre-optimization instruction-origin table into an optimized call-site
map.

As a second production control, the aggregator re-derived four bound lean-zip
profiles against exact release Wasm
`e20df1c562cf8a3acaf80ac2d0868660aa3afa2a7e8ad6a98a371687c8b1659d`
(936,072 bytes) and function sidecar
`22b304489260ccf819de7aef50359275943a69c3ddf11777f293e3153ca660cb`
(999,568 bytes). All artifact, sidecar, raw-profile, and workload identities
matched. The aggregate itself has SHA-256
`2929638eb6e65dcc2bb091cb99fc32a6fede9e653627d8ad134b24d1bac0152c`.

The leading median shares of Wasm self time were:

| Rank | Final function | Median share | MAD |
| ---: | --- | ---: | ---: |
| 1 | `Zip.Native.Deflate.lz77LazyMergedLoop` | 25.59% | 0.26 pp |
| 2 | `fir_dec_once` | 14.24% | 0.40 pp |
| 3 | `fir_byte_array_validate` | 5.93% | 0.18 pp |
| 4 | `Zip.Native.Deflate.chainWalkPackedUBelow._redArg` | 5.37% | 0.63 pp |
| 5 | `Zip.Native.Deflate.chooseSplitsHeuristicPUPacked.go._redArg` | 4.10% | 0.05 pp |

These are noisy attribution measurements, not elapsed-time performance claims.
They demonstrate that the final-function aggregator remains useful and
fail-closed independently of instruction provenance.

## lean-zip provenance scaling result

An ignored thin probe called the real `LeanZipFir.Compile.compileRaw` and the
generic `ModuleArtifact.writeInstructionOrigins` API. It did not copy the
compressor, resident linker, or origin serializer.

The ordinary frontier compiled in 50,505 ms and wrote in 4 ms. It contains
3,412 functions and 1,619,331 Wasm bytes. Baseline and diagnostic frontier
files were byte-identical at SHA-256
`1801c40995ac8b199b4e71ce4870ed6fcb3b5609ae1895018eca3a7b07ed1910`.

The diagnostic run was stopped after more than 310 seconds in provenance
generation following the same approximately 50-second compilation. It had not
published an origin table, so there is deliberately no table size, hash, or
origin-count claim for lean-zip.

The current serializer maps every function and then filters the complete
origin array for that function. Its visible construction is therefore
proportional to `functionCount * originCount` before JSON serialization. The
production timeout is consistent with that scaling, but no native sampled
profile was collected, so this note does not claim a lower-level runtime
hotspot.

## Decision and follow-up

1. Accept the W7-2 API and prettyM validation as release-neutral and useful.
2. Keep origin tables opt-in and unpackaged.
3. Preserve the strict separation between pre-optimization origins and
   exact-release final-function profiles.
4. Before repeating lean-zip, group the already ordered origin rows by function
   in one pass, making table construction proportional to functions plus
   origins. Avoid constructing one filtered copy of the complete origin array
   per function.
5. Rerun the same lean-zip probe with a bounded origin phase, then collect at
   least seven measured runs only if the repaired single run is practical.

This is a tooling scalability follow-up, not a compiler-semantics discrepancy
or a package-contract change.

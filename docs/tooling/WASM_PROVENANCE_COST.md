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

## Initial lean-zip provenance scaling result

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

## Repaired production result

W7-2 repaired the diagnostic path in `e28a67f1`. The serializer now consumes
the already ordered origin stream once instead of filtering the complete table
for every function. Fail-closed encoded-body and opcode validation remains in
place, but compares byte ranges in situ rather than allocating and immediately
releasing a slice for every check. The ordinary encoder and compact origin
schema are unchanged.

Profiling was necessary to find the second half of the repair. After the
one-pass grouping change alone, recursive slice destruction and repeated
`ByteArray.data` projection still dominated. In the final profile,
`lean_byte_array_data` fell below the 0.5% reporting threshold and recursive
destruction fell to 4.07% self time; ordinary interpreter and Array work became
the leading costs.

The production probe then completed seven measured lean-zip runs. Every round
reproduced the same ordinary/diagnostic Wasm and compact-table identities:

- 3,412 defined functions and 518,933 checked symbolic instruction origins;
- Wasm: 1,619,348 bytes, SHA-256
  `a311390c4c47d83eb7a856f3e9a591b58df6eacc9578fda21216d150fcf168b0`;
- compact table: 9,046,210 bytes, SHA-256
  `e4d6829e8cd3fe2f7dc63b040409613e857db67f50e428521a1d1f0f1b0d9406`;
- origin-phase milliseconds:
  `[15384, 14954, 16065, 13734, 16229, 13536, 15139]`, median 15,139 and
  median absolute deviation 926;
- complete wall seconds:
  `[45.48, 48.20, 49.02, 46.79, 51.99, 45.72, 52.29]`, median 48.20 and
  median absolute deviation 2.48;
- median peak RSS 4,892,680 KiB, median absolute deviation 124 KiB.

The size difference from the initial stopped probe reflects the newer compiler
and source closure used by both ordinary and diagnostic arms of the repaired
experiment. Within every repaired round, ordinary and diagnostic Wasm are
byte-identical. The canonical instruction-origin checker resolves all 518,933
rows to their recorded opcodes.

For the unchanged current prettyM input, the repair also preserves both files
byte-for-byte: 120,756-byte Wasm at
`576a9c5a3bb62fd6764e6c5cd431f074127617b5bddc16045142644f089fb959`
and 605,161-byte origin JSON at
`75d6d99b664ae209925c134d04c3d8ff78694654f613897acd936e8af80fba71`.
The complete artifact gate regenerated its 393-function, 35,622-origin table
twice in 94--96 ms.

## Decision and residual follow-up

1. Accept the W7-2 API and prettyM validation as release-neutral and useful.
2. Keep origin tables opt-in and unpackaged.
3. Preserve the strict separation between pre-optimization origins and
   exact-release final-function profiles.
4. Treat the production scaling issue as resolved by the ordered one-pass
   grouping and allocation-free byte-range validation.
5. Retain raw origin tables as regenerable diagnostics. Consider streaming or
   compression only if a concrete consumer needs the 9 MB lean-zip table; do
   not add it to ordinary immutable packages preemptively.

This was a tooling scalability repair, not a compiler-semantics discrepancy or
a package-contract change.

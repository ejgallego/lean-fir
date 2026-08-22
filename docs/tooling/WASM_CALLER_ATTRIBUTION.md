# Exact-release Wasm caller attribution

Status: validated on 2026-08-22 against the retained prettyM and lean-zip
production profiles. This is sampled attribution evidence, not a dynamic call
count or elapsed-time comparison.

## Method

`fir.sampled-profile-aggregate/v2` assigns every sampled Wasm leaf to its
immediate parent node in the V8 CPU-profile tree. It preserves four cases:

- an exact final Wasm function from the verified function sidecar;
- a recursive edge when caller and target have the same final index;
- an explicit host/runtime frame; or
- an explicit root when V8 supplies its `(root)` node or no parent.

The report gives each edge's share of all Wasm self samples and its conditional
share of the target function's self samples. Conditional shares are summarized
only over runs in which the target was sampled. Medians from separate edges do
not necessarily sum to one.

Malformed profile graphs fail closed. Duplicate node ids, missing children,
multiple parents, parent cycles, and sampled or caller Wasm indices outside the
exact sidecar are rejected. Every accepted run checks that the caller-edge
sample total equals its Wasm self-sample total.

The pinned external tooling gate additionally collects a fresh Node Inspector
profile from an ordinary Binaryen-built fixture, invokes the aggregate-v2 CLI,
checks caller coverage for every sampled function, and requires the concrete
`Fixture.entry` to `Fixture.leaf` Wasm caller edge. Synthetic unit cases retain
the malformed-graph and recursive/host/root boundary checks.

## Production controls

Both controls reused four untouched, semantically checked CPU profiles from
the post-checked-Nat W7 campaign. The reports remain ignored evidence under the
tooling worktree's `.deps/evidence/` directory.

| Workload | Wasm identity | Sidecar identity | Attributed samples | Report identity |
| --- | --- | --- | ---: | --- |
| prettyM | 120,739 bytes; `06cb977f...0119` | 164,320 bytes; `569c327a...b04` | 2,358 | 719,878 bytes; `3ad00c8a...ca86` |
| lean-zip | 936,072 bytes; `e20df1c5...b1659d` | 999,568 bytes; `22b30448...60cb` | 15,334 | 1,636,789 bytes; `57b0633e...3813` |

All eight runs had zero unresolved Wasm samples and exact equality between
Wasm self samples and caller-attributed samples. The report embeds the complete
artifact, sidecar, evidence, raw-profile, workload, runtime, observation, and
window identities; abbreviated hashes above are only for readability.

## `fir_dec_once`

prettyM spends a median 9.55% of Wasm self samples in `fir_dec_once`. Its
leading immediate caller shares of that target are:

| Caller | Target-self median | Wasm-self median | Present runs |
| --- | ---: | ---: | ---: |
| recursive `fir_dec_once` | 19.23% | 2.02% | 4/4 |
| specialized `Std.Format.be`/`prettyM` worker | 17.74% | 1.68% | 4/4 |
| root | 11.06% | 1.06% | 4/4 |
| `fir_release_3` | 9.35% | 0.94% | 4/4 |
| `fir_release_1` | 9.93% | 0.93% | 4/4 |
| `fir_release_0` | 8.87% | 0.86% | 4/4 |
| specialized `Std.Format.pushGroup` worker | 8.75% | 0.85% | 4/4 |
| `Std.Format.spaceUptoLine'` | 8.75% | 0.83% | 4/4 |

lean-zip spends a median 14.24% of Wasm self samples in `fir_dec_once`. Its
leading caller shares are:

| Caller | Target-self median | Wasm-self median | Present runs |
| --- | ---: | ---: | ---: |
| `Zip.Native.Deflate.lz77LazyMergedLoop` | 49.25% | 6.79% | 4/4 |
| root | 22.33% | 3.18% | 4/4 |
| `Zip.Native.Deflate.lz77ChainLazyIterPMerged` | 8.99% | 1.32% | 4/4 |
| `Zip.Native.Deflate.chainWalkPackedUBelow._redArg` | 7.42% | 1.09% | 4/4 |
| `Zip.Native.Deflate.tokenFreqsPTA.go` | 4.66% | 0.66% | 4/4 |
| `fir_ext_Array_set` | 3.47% | 0.50% | 4/4 |

Root attribution is retained as an observed profiler boundary. In particular,
the report does not invent a caller across an elided or tail-called frame.

## Allocation interpretation

prettyM's `fir_alloc_ctor_10`, the two-object-field `List.cons` shape, remains
8.72% of Wasm self samples. Its four stable callers are the specialized
`Std.Format.be` lambda and worker, `pushGroup`, and `spaceUptoLine'`; their
conditional medians are 29.59%, 32.14%, 16.75%, and 20.09%. The same source
region also supplies the main non-release-helper callers of `fir_dec_once` and
`fir_inc_0`.

That is useful locality evidence, but not evidence that recursive release is a
List-only cost. In lean-zip, `fir_alloc_ctor_11` is only 0.04% while
`fir_dec_once` is dominated by compression loops and Array updates. The shared
result therefore supports evaluating the upstream-shaped generic release fast
path first. Constructor initialization and physical-shape consolidation remain
separate follow-ups after the carrier/provenance boundary is stable.

# Wasm instruction-profile consumer

Status: real-consumer compatibility checkpoint. This does not define a package
schema or change the canonical release artifact.

## Decision

The existing Node Inspector profile remains a final-function consumer only.
Node 24.19.0 also accepts V8's experimental `--perf-prof-annotate-wasm` flag,
but its embedder does not install the Wasm source-map loader required by that
path. A `perf` capture therefore resolves the optimized Wasm function and its
native PCs, but the injected ELF has no debug-line table relating those PCs to
the module source map.

The first instruction-level consumer should be V8's `d8` perf path:

```text
perf record -k 1 ... -- d8 \
  --perf-prof \
  --perf-prof-annotate-wasm \
  --perf-prof-unwinding-info ...
perf inject --jit -i perf.data -o perf.jit.data
```

This is deliberately a diagnostic-only path. The normal Node/browser
benchmark continues to execute the exact stripped release with no source map,
instrumentation, or profiler flags. FIR should not add a native Node addon or
an instrumented module merely to make the current profiler consume a map.

V8's implementation makes the embedder boundary explicit. The perf logger
reads the module's source map and emits native-PC debug entries keyed by source
filename and one-based line. Its column is fixed to one. The `d8` shell
installs the necessary `WasmLoadSourceMapCallback`; Node does not currently do
so. The relevant upstream sources are:

- <https://chromium.googlesource.com/v8/v8/+/refs/heads/main/src/diagnostics/perf-jit.cc>
- <https://chromium.googlesource.com/v8/v8/+/refs/heads/main/src/d8/d8.cc>
- <https://chromium.googlesource.com/v8/v8/+/refs/heads/main/tools/profiling/linux-perf-d8.py>

The first real `d8` gate exposed two compatibility boundaries. V8 15.4.29
rejects the standard one-field unmapped segment at the end of Binaryen's exact
map, and its JIT event carries only one filename for an entire Wasm function.
W7-2's accepted diagnostic projection addresses both without changing the
authoritative map: every segment uses one fixed profiling filename, while a
separate legend maps dense one-based line IDs to exact FIR origins or the
reserved explicit-unknown token. The repeat consumer gate is recorded below.

## Minimum location key

The perf consumer exposes:

```text
(fixed profiling source filename, one-based legend line ID)
```

It does not expose a final Wasm bytecode offset, a source-map column, or an
inline stack. V8's `JitLogger::LogRecordedBuffer` chooses the filename from the
first valid source-map entry and later entries contribute line numbers only, so
distinct per-origin source filenames cannot preserve intra-function changes.
The profiling projection instead allocates one stable line ID per complete
origin-table row and reserves line 1 for explicit unknown. Tooling resolves the
line through the checksummed legend. Repeated, missing, or multiply resolved
IDs fail closed; they are never repaired by instruction order.

The origin row needs only the compiler facts already proposed by W7:

- stable origin identity;
- symbolic function identity;
- structured instruction path or preorder identity;
- symbolic opcode; and
- direct-call target when the instruction is a call.

## Release-bound sidecar

A first consumer sidecar must bind:

- schema and location-key versions;
- canonical stripped release byte length and SHA-256;
- mapped companion byte length and SHA-256;
- final source-map byte length and SHA-256;
- profiling-projection byte length and SHA-256;
- profiling-legend schema, row count, byte length, and SHA-256;
- origin-table byte length and SHA-256;
- exact Binaryen version and ordered transformation arguments;
- the final function-index sidecar SHA-256;
- source filename and one-based line for each mapped origin; and
- explicit mapped, deleted, unknown, and ambiguous counts.

The companion must strip to the independently generated canonical release.
The verifier rejects hash drift, duplicate location keys, a source-map entry
without an origin, or an origin classified both mapped and deleted. A native
PC without debug-line information is `unknown`, not a nearest-neighbor match.

The fixed profiling filename and legend line are sufficient as the identity
carried by a native-PC annotation. They are not, by themselves, a complete
sidecar: the authoritative sidecar must still retain final instruction
identity and explicit mapped, deleted, unknown, and ambiguous states. A
consumer-specific source-map projection must not silently turn an unmapped
interval into the nearest preceding origin.

## Node feasibility evidence

The probe consumed W7-2's ignored two-module fixture at branch
`wasm/generic-array-validation`, commit `8b67f0da`. Its release SHA-256 was
`dcd66e4279859b4770c7f602413acae72f97d94cff82c0d911fb0927831e1f53`.
The source-map-bearing module and map used for the Node capture had SHA-256:

```text
c2b52e745e891eff986350d3098303b9cca0c1e127994bc1b8b7aa6260ab32e7  pipeline-url.wasm
2ebd0c003198538057428bacad20e0cb35dce5e641305be9f05e2376e34716fb  pipeline-url.map
```

The accepted capture used Node 24.19.0, perf 6.19.10, `cycles:u` at 997 Hz,
inherited sampling, monotonic clock id 1, and a 100,000-call warmup followed by
5,000,000 measured calls. The endpoint was exactly 5,100,000. It recorded 145
samples; the optimized Wasm entry was present as `JS:entry-0-turbofan`.
After `perf inject --jit`, its generated ELF contained `.text` and `.symtab`
but no `.debug_line` section. Raw evidence is retained under the tooling
worktree's ignored `.deps/instruction-profile/run-03/` with these hashes:

```text
a39f502fa253a3cf168778252f55494935e3ed7752b697edfef7d32f873c165c  perf.data
c22529f9235ca2a93588dcacb4c15a8405eef04ebebdd1f138beb0e7a8ad1abe  perf.jit2.data
4dbd4d07e595155be33f7283f62d5dfbb43ea97f11d6657ece2a6f5cf4301a41  jit-6.dump
8d959b03fa3c68fedacfe4214892ef955c70ff64eae7d2f1fe7248e174b0f87f  jitted-6-2415.so
```

The first rejected capture omitted `perf record -k 1`; `perf inject` correctly
rejected the clock mismatch. Any future wrapper must enforce the monotonic
clock and reject an injected profile that lacks both the expected Wasm symbol
and debug-line entries.

## Real d8 gate evidence

The gate consumed W7-2's deterministic optimizer fixture from original handoff
commit `7444a33b`, now landed without artifact drift as `8ff33577`. The exact
ignored outputs had these identities:

```text
850b6fae3fdc9761585dda42baf99b3e15aa5001e14adaa4c4cf8cd526b8427c  instruction-provenance.wasm
c9cfaf027b3da1529fd4d26e95b34eb76b7dcc1a6e5362d2a064c9d1f2355722  instruction-provenance.map
9705368cff660e5b18c827a4c6791db802081c36c76badee50ee3e5c2a38954a  instruction-provenance-report.json
```

The report binds a 58-byte canonical release at SHA-256
`0cf51807b1ccedeedbc81293acd275cd17d86b2ba2e186fc383e80a2d888a1b8`.
It classifies seven keys as mapped and five as deleted, with zero optimizer
unknowns, ambiguities, or repeated mappings. The companion remains 121 bytes,
has no imports, and exports only `fixture.entry`.

The consumer was `d8`/V8 15.4.29, installed by `jsvu` 3.0.5 from V8's official
Linux x64 release archive. The `d8` binary SHA-256 was
`ce93362b4ef8170a2b51cbe99aed57cda82613eb6dfc5f24a0f411c61a470b5b`.
The host used perf 6.19.10 on Linux 7.1.5-070105-generic x86-64, with
`kernel.perf_event_paranoid=2` and `kernel.kptr_restrict=1`.

The exact-map control kept the small fixture out of JS-to-Wasm inlining and
forced its Liftoff debug source-position path so absence of a line table could
not be blamed on the fixture's normal tiering behavior:

```text
perf record -k 1 -F 997 -o perf.data -- d8 \
  --perf-prof --perf-prof-path="$PWD/jit" \
  --perf-prof-annotate-wasm \
  --liftoff-only --wasm-debug-mask-for-testing=1 \
  --no-turbo-inline-js-wasm-calls \
  --no-wasm-in-js-inlining-body \
  --no-wasm-in-js-inlining-wrapper \
  driver.js -- instruction-provenance.wasm 100000000
perf inject --jit -i perf.data -o perf.jit.data
```

It captured 2,570 samples and resolved `JS:entry-0-liftoff`, but the injected
ELF had no `.debug_line` section and no synthetic filename. The exact map ends
in `,C`, a valid one-field unmapped segment. V8's
`WasmModuleSourceMap::DecodeMapping` consumes four fields unconditionally and
therefore rejects that segment. The raw exact-control hashes were:

```text
635f15b486b07f93d2f013ac49c7ffb7421fa95e84e3cc66c2b94aa5802cb36e  perf.data
2c75937ecd21414b9633fcbbfba358527ec3cf413cae7e657c3c985420e8586d  perf.jit.data
fa805527dea0e66d006441403e5a70e2a98e4bfeb676b207d40df4969797693f  jit-7.dump
d068404c6ae020b2f5c4a6f685c69eae0025cc7e8dd639ea5f9027618ba9bdaf  jitted-7-2528.so
```

For diagnosis only, removing that terminal unmapped segment produced a
four-field-only map at SHA-256
`44b76cfa88cbc53dc04ffbbbbd2acf735e66ec3ef0143777547a1d6d5eb2dc1d`.
With otherwise identical settings, `perf inject` emitted a native line-table
entry at PC `0x102` for the expected key
`fir-wasm-origin/1/fixture.entry:1`. This proves that the chosen filename and
one-based line survive the `d8` JIT-dump path. It is not an accepted fix:
Binaryen's source-map disassembly shows that removing the sentinel extends
`fixture.entry:7` to the function close. The authoritative exact report keeps
the five deleted keys distinct, and consumer PCs lacking an exact annotation
remain explicitly unknown.

## Accepted repeat gate

W7-2 implemented the single-file line-ID projection at original handoff commit
`4eebbdae`, now landed without artifact drift as `b01f203b`. The canonical
release, companion, and exact Binaryen map remain unchanged. The additional
deterministic artifacts are:

```text
57b954865e27242c6043da3fd2767201004067570618216c49b11b69cc10a72e  first-profiling.map, 123 bytes
cc19ac9f429560515f00382e9182c5fa157088706064aa30aea4a45a0330a433  first-profiling.legend.json, 1,497 bytes
b4fbea0d3a513a58b3971e51005171564c0ff96ff6f91880aa764ef06c17dbb1  first-report.json, 1,671 bytes
```

The legend has schema `fir.wasm.instruction-profile-legend/v1`, uses the fixed
source `fir-wasm-profile/profiling-v1`, reserves line 1 for
`fir-wasm-unmapped/profiling-v1`, and assigns dense lines 2 through 13 to the
complete pre-optimization origin inventory. Resolving the projected map
through that legend reproduces seven mapped and five deleted exact origins,
one explicit profiling-gap token, and zero ambiguous origins. Deleted origins
are not reassigned.

Tooling regenerated all six identities directly from committed source before
the consumer run. This was necessary because the producer's mutable `_build`
directory had retained the new map and legend but a stale report after its
worktree switched branches. Producer-to-consumer handoffs should therefore
publish or freeze a complete output set atomically.

The accepted repeat capture used the same pinned V8 15.4.29 binary and
100,000,000-call Liftoff-debug workload. It completed with checksum
`1343710208`, retained 3,253 samples with zero lost, and attributed 8.09% self
time to `JS:entry-0-liftoff`. d8 accepted the projection and the injected ELF
contained profiling line 5 at native `0x102`; legend line 5 resolves exactly to
the authoritative mapped token `fir-wasm-origin/1/fixture.entry:1`. V8 emitted
no row for the terminal reserved line-1 gap and the line-5 range was
zero-length, so sampled hot PCs remain unresolved. Controls with arithmetic,
control flow, and memory established that V8 places these experimental rows on
cold or terminal native ranges. Requiring a resolved hot sample here would test
V8 range coverage rather than FIR provenance, so that criterion is explicitly
deferred.

Raw accepted-repeat identities are:

```text
e7e0451f300277bf751f4fdcd3517730e3a03d57a6e350cdba7b6102d578144a  perf.data
d933d7efd2b22376b8ee348364b87c7d3388a501af1694480e324cb6c6eb37be  perf.jit.data
1055b8da345b3bf8d6f8652cd7fc774cbe76e2fab1ae1448de47295836589bd3  jit-6.dump
80e62ab4179af32da8d2506ba5455d56050d20259aa49409b013e49d0c62ca51  jitted-6-2528.so
```

This completes the consumer/projection decision. Package-schema stabilization,
representative size and generation-time measurements, and a consumer with
verified hot-code native ranges remain separate future work.

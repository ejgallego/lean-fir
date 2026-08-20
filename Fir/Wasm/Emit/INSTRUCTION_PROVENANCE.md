# Exact-release Wasm instruction provenance checkpoint

Status: feasibility checkpoint only. This document does not define a stable
package format and does not change the emitter, optimizer flags, or benchmark
artifact.

## Question

The existing `fir.wasm.function-index/v1` evidence resolves a sampled final
Wasm function to its Lean or resident-runtime identity without assuming that
linking and optimization preserve function order. The next profiling question
is narrower: can a final instruction range or call site be related to the FIR
operation that emitted it after resident linking, dead-code elimination,
function reordering, and Binaryen optimization?

Two requirements control the design:

1. the canonical stripped release remains byte-for-byte unchanged; and
2. deleted, synthesized, or ambiguously transformed code is classified rather
   than assigned an origin by position.

## Feasibility result

A worktree-local two-module fixture exercised the external-runtime pipeline:

1. a frontier module exported `fixture.entry`, imported one runtime helper,
   and carried distinct synthetic locations on its argument and call;
2. a runtime module defined that helper and one unreachable function;
3. Binaryen assembled both modules with source maps, merged them, ran
   meta-DCE, reordered functions, and optimized the result with `-O3`; and
4. the mapped companion was stripped and compared with a parallel canonical
   release built with the ordinary stripping flags.

The optimizer inlined the runtime helper into `fixture.entry`. All three
surviving non-structural expressions retained an origin: the final `i32.add`
and constant mapped to the runtime helper, while the final `local.get` mapped
to the frontier entry. The frontier call site and both dead functions were
absent, as expected. The fixture therefore had 3/3 mapping coverage for
surviving expressions, with deleted identities represented by absence rather
than positional inference.

The canonical release and the stripped mapped companion were both 50 bytes
and had SHA-256:

```text
dcd66e4279859b4770c7f602413acae72f97d94cff82c0d911fb0927831e1f53
```

The unstripped mapped companion was 67 bytes and its source map was 156 bytes.
An alternating 15-round process-level timing probe measured the complete tiny
fixture pipeline, including assembly and the final companion-strip identity
check. The ordinary path had a 30.21 ms median (28.02--32.39 ms), while the
mapped path had a 35.98 ms median (33.38--38.08 ms): 5.77 ms, or about 19%, of
median overhead. Process startup dominates a fixture this small, so this is a
reproducibility cost bound rather than a representative package-build ratio.
The size measurements likewise establish technical transport rather than a
representative package cost.

Standard source maps associate a surviving output expression with one source
location. They do not encode a complete inline stack. In this fixture the
inlined arithmetic retained the callee's origin, but the eliminated call-site
identity did not also survive. A first schema must not claim inline ancestry
that this transport cannot prove.

## Consumer boundary

The same fixture was profiled through Node 24's Inspector API with a 100
microsecond sampling interval and 20,000,000 calls. Its Wasm nodes reported the
function/start column (`43`), while every `positionTicks` entry contained only
line 1. The existing lean-zip CPU profile has the same shape. The current
profile can identify a final function but supplies no sampled instruction
offset with which to query an instruction map.

Consequently, emitting a source map now would preserve useful provenance and
improve diagnostic naming, but it would not by itself provide hot call-site
attribution to the current profiler. Tooling must first select a consumer that
exposes final Wasm bytecode positions. V8 advertises an experimental
source-map-aware `perf` mode; that and debug-companion DevTools or opt-in
instrumentation are consumer candidates, not assumptions in the compiler
schema.

## Proposed narrow compiler surface

The least disruptive W7 surface is an additive encoder result rather than a
new field on every symbolic `Instruction`:

```text
encodeWithOrigins(module) -> {
  bytes,
  instructionOrigins
}
```

`bytes` must equal the existing encoder output. `instructionOrigins` records
the encoded byte offset of each emitted symbolic instruction together with a
stable origin allocated after FIR resident linking and dead-code elimination,
before binary encoding. A first origin can contain:

- symbolic function identity;
- structured instruction path or preorder identity within that function;
- symbolic opcode; and
- direct-call target when the instruction is a call.

This does not yet promise an LCNF operation, block, source span, or inline
ancestry. The current symbolic Wasm `Instruction`, `Function`, and `Module`
types carry no source locations, and the lowering path returns plain
instruction lists without retaining an operation-to-instruction relation.
Inventing those fields from final order would violate the fail-closed rule. A
later lowering trace may relate LCNF structural operation paths to these
symbolic instruction origins without changing the semantic instruction type.

The encoded offsets can seed a synthetic input source map. Each Binaryen stage
then consumes the preceding map and emits the next map. The diagnostic output
is retained until its final map is written; stripping that output must
reproduce the independently generated canonical release exactly.

## Proposed evidence boundary

No schema is accepted yet, but a viable first sidecar must bind at least:

- canonical stripped release byte length and SHA-256;
- mapped companion byte length and SHA-256;
- final source-map byte length and SHA-256;
- origin-table byte length and SHA-256;
- exact Binaryen version and ordered arguments for every transforming stage;
- the existing final function-index sidecar identity; and
- explicit counts for mapped, deleted, and unknown origins.

Verification fails closed if an artifact or dependency hash differs. Final
expressions without a carried location are `unknown`; pre-optimization origins
not present in the final map are `deleted`. Neither class is repaired by
zipping source and output positions.

An optional final-layout name-section companion is independently feasible and
useful for readable DevTools labels. It is not instruction attribution. It
must also strip to the canonical release, or have its non-custom and code
sections proved identical.

DWARF is not the first mechanism. Retaining fully valid DWARF constrains some
Binaryen transformations, while source-map locations already survive the
pipeline without changing release optimization.

## Sequenced next slices

1. Tooling selects and checks a profiler or diagnostic consumer that exposes a
   final instruction location.
2. W7 adds the additive encoder trace and a checked assertion that its `bytes`
   equal the ordinary encoder output.
3. W7 promotes the two-module fixture into a deterministic gate across merge,
   meta-DCE, reorder, and optimization, including release-byte identity and
   mapping-coverage assertions.
4. W7 and tooling agree on a versioned, release-bound sidecar only after the
   consumer's minimum location key is known.
5. Package integration remains opt-in until representative size and
   generation-time measurements are recorded.

This sequence keeps the generic compiler evidence independent of lean-zip and
avoids committing to an unconsumable package format.

## References

- Binaryen's official debug-information documentation describes source-map
  transport, WAT `;;@ file:line:column` annotations, location propagation, and
  the optimization limitations of retained DWARF:
  <https://github.com/WebAssembly/binaryen#debug-info-support>.
- The WebAssembly tool-conventions debugging document defines the standard
  source-map and DWARF conventions:
  <https://github.com/WebAssembly/tool-conventions/blob/main/Debugging.md>.

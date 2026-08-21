# Exact-release Wasm instruction provenance checkpoint

Status: additive encoder-origin trace, deterministic optimizer fixture, and
explicit profiling-map projection implemented. The real `d8` control confirms
the location identity but exposed one source-map compatibility boundary. This
document does not define a stable package format and does not change the
ordinary encoder, optimizer flags, or benchmark artifact.

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

Consequently, emitting a source map preserves useful provenance and improves
diagnostic naming, but does not by itself provide hot call-site attribution to
the current Node profiler. Tooling selected V8 `d8` with source-map-aware
`perf` annotations as the first instruction consumer. Its minimum key is a
synthetic source filename and one-based source line; it does not expose a
source-map column or inline stack. Node remains the exact-function consumer.

### Real d8 compatibility result

Tooling ran V8 15.4.29 from `jsvu` 3.0.5 with perf 6.19.10 against the exact
121-byte companion and 230-byte Binaryen map below. `d8` opened the map, but
its Wasm decoder requires four fields in every segment and rejected the final
standard one-field unmapped segment. The 2,570-sample exact capture retained
the expected `JS:entry-0-liftoff` symbol, but its injected ELF consequently had
no debug-line section or synthetic filename.

Removing that terminal segment for diagnosis made native PC `0x102` resolve to
`fir-wasm-origin/1/fixture.entry:1`, proving that filename plus one-based line
survives the `d8` JIT-dump path. That edit is not accepted: it extends the
preceding origin over the interval that Binaryen deliberately marked unmapped.
The exact map therefore remains authoritative.

The deterministic profiling projection instead replaces each one-field gap
with a unique line in the reserved non-origin source
`fir-wasm-unmapped/profiling-v1`. It does not alter any mapped segment. A native
PC on one of those lines is explicitly `unknown`, never a neighboring origin;
pre-optimization origins absent from the exact map remain `deleted`. This map
is a diagnostic compatibility view, not a standards-correct replacement for
the exact Binaryen map.

## Proposed narrow compiler surface

The implemented W7 surface is an additive encoder result rather than a new
field on every symbolic `Instruction`:

```text
encodeWithOrigins(module) -> {
  bytes,
  origins
}
```

The ordinary `encode` path remains unchanged. `encodeWithOrigins` first calls
that same internal encoder, then checks every function body and opcode against
the produced bytes before returning absolute module offsets. Any section,
body, or opcode drift fails closed. Each origin contains:

- symbolic function identity and absolute pre-optimization Wasm function
  index;
- structured instruction path and preorder identity within that function;
- exact opcode bytes and complete encoded symbolic-instruction size;
- direct-call target when the instruction is a call;
- absolute opcode byte offset in the module; and
- a unique synthetic source filename and one-based source line.

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

The Lean fixture contains nested and top-level `i32.add` instructions with the
same opcode, plus a direct call. It checks ordinary/traced byte identity,
absolute opcode agreement, distinct structured paths, sequential source lines,
function indices, and exact call-target retention.

The external two-module fixture runs twice through assembly, merge, meta-DCE,
function reorder, and `-O3`. Its optimized entry retains two same-opcode add
sites from different source functions while eliminating the call. Both runs
produce the same 58-byte release, 121-byte mapped companion, 230-byte source
map, and classification report. Stripping the companion reproduces the
canonical release at SHA-256:

```text
0cf51807b1ccedeedbc81293acd275cd17d86b2ba2e186fc383e80a2d888a1b8
```

The final classification is seven mapped, five deleted, zero unknown, and zero
ambiguous origin keys. In particular, both surviving additions remain mapped
and the inlined call site remains deleted rather than being reassigned.

The exact map remains 230 bytes at SHA-256
`c9cfaf027b3da1529fd4d26e95b34eb76b7dcc1a6e5362d2a064c9d1f2355722`.
The V8-compatible profiling projection is 267 bytes at SHA-256
`96680e47878348d162820e6fe022e053c8743704697a7a36d9379efe6b9581fd`;
it retains the same seven mapped and five deleted origin identities and adds
exactly one explicit profiling-gap identity. Both maps are generated twice and
compared byte-for-byte by the artifact gate.

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

## Remaining sequence

1. Repeat the real `d8 --perf-prof` capture with the explicit profiling
   projection. The injected debug-line table must contain both a surviving
   origin and the reserved gap line, and no deleted origin may be reassigned.
2. After that repeat gate, W7 and tooling may agree on a versioned,
   release-bound sidecar. The current Lean structures and projection are APIs,
   not that package schema.
3. Package integration remains opt-in until representative size and
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

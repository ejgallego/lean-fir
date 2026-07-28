# FIR Wasm artifact lane

This package turns the supported W3--W5 semantic FIR corpus into deterministic WebAssembly 1.0
binary artifacts, then runs those artifacts in standard Node and browser
`WebAssembly` engines with both the established semantic FIR host and an
incrementally widened concrete wasm32 linear-memory host.

The corpus covers erased and maximum-width unsigned results and entry arguments, tagged
argument handles, tagged and heap-allocated natural literals, heap strings, constructor
allocation and projection, exact and default constructor cases, and a transitively
reachable constructor graph. W5 fixtures additionally execute packed `USize` and scalar
projection/mutation, object and tag mutation, reference counting, unique and shared
reset/reuse, and the structured dead-object fault after deletion. Each `.wasm` file is
accompanied by a manifest that derives
its entry parameter and result ABI, records its semantic inputs, and describes its semantic
runtime imports. The separate `FirWasmOracleMain.lean` program runs the same named corpus
through the current FIR/Talos semantic oracle and writes its comparable observations beside
the artifacts. The Node runner compares V8 directly with those live results; no expected
semantic observations are frozen in the emitter.

The concrete runners currently execute 43 closed artifacts through raw scalar
lanes, wasm32 tagged words, checked 32-byte object headers, eight-byte semantic
slots, natural, UTF-8 string, and constructor allocation, cases/projection, ordinary and
recursive direct calls, single/multi-stage closure application, object/tag
mutation, balanced and recursive ownership updates, deletion, unique/shared
reset/reuse, recursive cache publication, and maximum-width integer
boxing/unboxing, an effect-producing external echo, and a twice-called cached
external with one physical miss/effect/hit sequence. The packed-scalar corpus
includes compiler-shaped mutation/readback for all four supported integer
widths. Their
logical-location map and allocation descriptors are observation-only data;
runtime imports exchange physical words and consult the byte-level heap. Node
and a Fetch-only browser Worker import the same host, explicit foreign
registry, and fixture inventory. Missing foreign implementations fail with a
structured reject-by-default fault. Packed initial constructors and other
initial heap kinds stay on the semantic runner until their concrete
counterparts join this explicit allowlist; unsupported runtime operations are
still rejected while constructing the concrete import object.

The concrete host also reconstructs the object-field constructor, arbitrary-
precision natural, and UTF-8 string subset of `initialRuntime`. It reserves physical addresses
for the complete heap before writing references, preserves semantic location
order and cell metadata, and then passes the mapped address to a compiler-
produced `List Nat` classifier. Node and the browser Worker audit every loaded
cell and the entry-argument round-trip before executing it. A compiler-produced
Unicode string input is audited and executed through the same path; packed
constructors and the other initial heap kinds are not silently admitted.

The historical hand-written `mutation` fixture is intentionally not in that
success allowlist: it uses packed-scalar slot index `1` despite a one-object,
one-`USize` prefix. The concrete runner asserts its exact
`scalarFieldMissing(1, 0)` failure, while `compiler-shaped-mutation` uses Lean
4.32's emitted index `2` and passes `USize` plus `UInt64` write/read execution.

The W5 corpus also covers an effect-producing external call and a zero-argument
external cached across two source calls. V8 and Talos agree on the returned
values, the single cache miss, world advancement, and the exact external trace.
Direct calls, saturated and underapplied closures, and recursion execute as
ordinary Wasm calls around the semantic closure metadata imports.
Compiler-produced source fixtures also cover heap-backed string and `List Nat`
arguments through the explicit initial-runtime manifest. The semantic host is
shared with the repository's native↔V8 validation adapter, whose generated
corpus now also round-trips immediate and heap `Int` values and exact
`ByteArray` boundary payloads.

Run the complete lane-local check with:

```text
./check.sh
```

The resident-global compatibility probe checks the shared state surface used
by the forthcoming Wasm-owned heap frontier. Resident globals follow all
lazy-cache flag/value globals, preserve typed nonzero initializers, and remain
mutable:

```text
lake exe fir-wasm-artifact resident-global _build/resident-global.wasm
node run-resident-global.mjs _build/resident-global.wasm
lake exe fir-wasm-artifact resident-memory-surface \
  _build/resident-memory-surface.wasm
node run-resident-memory-surface.mjs _build/resident-memory-surface.wasm
lake exe fir-wasm-artifact resident-allocator \
  _build/resident-allocator.wasm
node run-resident-allocator.mjs _build/resident-allocator.wasm
lake exe fir-wasm-artifact resident-constructors \
  _build/resident-constructors.wasm
node run-resident-constructors.mjs _build/resident-constructors.wasm
lake exe fir-wasm-artifact resident-closure-allocation \
  _build/resident-closure-allocation.wasm
node run-resident-closure-allocation.mjs \
  _build/resident-closure-allocation.wasm
lake exe fir-wasm-artifact resident-literals \
  _build/resident-literals.wasm
node run-resident-literals.mjs _build/resident-literals.wasm
lake exe fir-wasm-artifact resident-setters \
  _build/resident-setters.wasm
node run-resident-setters.mjs _build/resident-setters.wasm
lake exe fir-wasm-artifact resident-tag-setter \
  _build/resident-tag-setter.wasm
node run-resident-tag-setter.mjs _build/resident-tag-setter.wasm
lake exe fir-wasm-artifact resident-increments \
  _build/resident-increments.wasm
node run-resident-increments.mjs _build/resident-increments.wasm
lake exe fir-wasm-artifact resident-releases \
  _build/resident-releases.wasm
node run-resident-releases.mjs _build/resident-releases.wasm
```

W7 also emits the first standalone Wasm-resident runtime slice. Its module
defines and exports one-page memory, has no imports, and exports the raw
`tobject → UInt32` helper `fir_getTag`. The browser-neutral smoke client writes
ordinary W6 immediate, constructor, and promoted-tag layouts directly into the
exported memory; no JavaScript runtime handler participates in the calls:

```text
lake exe fir-wasm-artifact resident-get-tag _build/resident-get-tag.wasm
node run-resident-get-tag.mjs _build/resident-get-tag.wasm
lake exe fir-wasm-artifact resident-is-shared _build/resident-is-shared.wasm
node run-resident-is-shared.mjs _build/resident-is-shared.wasm
lake exe fir-wasm-artifact resident-read-projections \
  _build/resident-read-projections.wasm
node run-resident-read-projections.mjs \
  _build/resident-read-projections.wasm
lake exe fir-wasm-artifact resident-closure-projections \
  _build/resident-closure-projections.wasm
node run-resident-closure-projections.mjs \
  _build/resident-closure-projections.wasm
lake exe fir-wasm-artifact resident-closure-matches \
  _build/resident-closure-matches.wasm
node run-resident-closure-matches.mjs \
  _build/resident-closure-matches.wasm
```

All standalone runtime modules and their `.wasm.json` descriptors are generated
deterministically. The `isShared` module implements the valid-input portion of
`isShared`: immediates and persistent/non-unique heap objects return one,
while a unique live heap object returns zero. The 983-byte projection module
exports the exact four object and four packed-`UInt8` reads reachable from
compiler-produced Lean 4.32 `prettyM`. Raw-header and concrete-host checks
exercise all eight helpers; recognized non-heap, misaligned, dead, and
non-constructor inputs trap without invoking JavaScript. The 1,466-byte
closure-projection module exports the twelve distinct capture slot/result
readers underlying 87 `prettyM` operations and checks the same direct-memory
boundary for closure layouts. The 635-byte closure-match module distinguishes
target, arity, and fixed-count mismatches directly in memory and checks both
raw layouts and concrete-host allocations. These are generation-readiness
artifacts, not the later theorems that the linked helpers satisfy the W6
contracts on related states. Setting `FIR_BROWSER=google-chrome` while running
`./check.sh` executes the same smoke clients in a browser Worker alongside the
existing `prettyM` check.

The 1,015-byte constructor module also has zero imports and owns its memory.
It checks both immediate empty constructors and exact nonempty W6 headers,
object slots, `USize` slots, packed scalar bytes, zero padding, repeated
allocation, frontier movement, and preservation of the temporary retagging
scratch word.

The 1,253-byte closure-allocation module likewise owns memory and has zero
imports. It freezes the W6 closure header, stable target and descriptor IDs,
zero-capture and mixed `tobject`/`UInt8`/`USize` capture slots, frontier
movement, and scratch preservation. Its deliberately shifted dispatch and
descriptor tables ensure resident linking cannot accidentally derive either
ID from the surviving import order. `ConcreteHost` independently decodes the
Wasm-born closures and projects every capture.

The resident literal module likewise has zero imports and owns its memory. It
checks immediate `Nat` encodings plus empty and Unicode/newline strings,
including the exact versioned W6 header, canonical UTF-8 payload, aligned zero
padding, frontier movement, scratch preservation, and direct `ConcreteHost`
decoding.

The 486-byte resident-setter module likewise has zero imports and owns its
memory. It performs guarded object-slot and packed-`UInt8` writes against an
exact raw W6 constructor header, traps on zero, misaligned, dead, out-of-bounds,
and width-mismatched inputs, preserves the scratch word, and lets
`ConcreteHost` independently project the written fields. These helpers perform
only the requested direct write; the LCNF's separate `inc` and `dec` operations
remain explicit.

The 230-byte resident tag-setter module likewise has zero imports and owns its
memory. Its fixed-tag helper validates an aligned live constructor, writes only
header `aux0`, restores the scratch lane, and traps on zero, misaligned, dead,
or non-constructor inputs. `ConcreteHost` independently reads the resulting
tag. Tags outside the W6 `UInt32` header lane fail during generation.

The 511-byte resident-increment module likewise has zero imports and owns its
memory. It implements overflow-checked nonrecursive increments, including
checked immediate and promoted-tag no-ops, persistent-object no-ops, ordinary
live-heap updates, and traps for invalid addresses, dead headers, unchecked
tagged representations, and overflowing counts. `ConcreteHost` independently
decodes the updated exact W6 headers.

Remaining JavaScript runtime operations can use that module-owned heap without
a facade. Construct the concrete host before instantiation as usual, then
attach the exported memory before allocating or invoking:

```js
const host = new ConcreteHost(
  manifest.imports,
  manifest.initialRuntime,
  undefined,
  manifest.closureDispatch,
  manifest.closureDescriptors,
);
const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
host.attachMemory(instance.exports.memory);
```

Attachment copies any initial heap prepared from the manifest, rejects
nonzero module memory and rebinding, and routes subsequent allocation and
growth through the same `WebAssembly.Memory`. This is the required transition
boundary for incrementally internalizing runtime imports without maintaining
two divergent heaps. `module-client.mjs` performs this attachment
automatically when the module exports `memory`, while rejecting hosts that do
not implement the concrete-memory boundary.

This builds the Lean emitter, runs the semantic oracle through Lean, emits the corpus and oracle
results twice, byte-compares all outputs, validates and instantiates every module in Node,
executes `main`, and compares the V8 observation with FIR. It requires Lean 4.32, the
worktree-local Talos setup, and Node; no external WAT or WebAssembly CLI is required. The
oracle uses `lean --run` so a fresh worktree does not native-compile the full upstream Wasm
semantics just to check this corpus.

The check also writes a deterministic, fail-closed concrete-switch readiness
report into each temporary artifact directory and byte-compares the two
copies. The current emitted corpus is fully classified and concrete-resolvable:
43 fixtures match the live FIR oracle, and the historical `mutation` fixture
retains its one exact expected concrete-layout fault. Two previously omitted
but already executable fixtures, `reference-counting` and `delete-fault`, are
part of that oracle-matched corpus.

The same report preflights all 13 compiler-produced source artifacts, and all
13 are concrete-resolvable. A shared Node/browser inventory gate also executes
all 11 invocation manifests and both invocation-free modules through the
concrete memory ABI, checking frozen results and exact initial-heap round trips.
The concrete registry executes all five integer, five
natural, eight UTF-8/string, and two unreachable-fallback declarations retained
by `prettyM`; focused tests cover immediate/heap integer boundaries, large heap
naturals, Unicode byte/code-point navigation, fresh results, stale inputs, and
exact fallback traps. Packed initial-constructor loading validates the
compiler-shaped fixed-slot coordinate and scalar range, derives the minimal
packed extent, and writes all four integer widths little-endian. The
all-constructor `prettyM` manifest now round-trips its 23-cell initial heap and
executes concretely in Node and the browser. Every module-local import site is
mapped to its runtime operation and current `W6-COVERAGE.md` cell. This is an
artifact/readiness audit: it deliberately does not claim W6 proof completion.
The shared validation product gate now executes 65 of 95 compiler-produced
cases through concrete wasm32 memory in both Node and the browser, comparing
each result and projected Nat effect with the canonical V8 observation. The
remaining 30 cases fail closed against an explicit inventory because they all
contain initial `ByteArray` objects; some additionally require the matching
concrete `ByteArray` external family.

A standalone report can be generated after the source and artifact manifests
exist with:

```text
node concrete-readiness.mjs ARTIFACT_DIR _build ../W6-COVERAGE.md readiness.json \
  --require-artifact-ready
node test-concrete-readiness.mjs readiness.json
```

To emit one fixture manually:

```text
lake exe fir-wasm-artifact literal /tmp/fir-wasm-corpus/literal.wasm
lake -d .. env lean --run ../FirWasmOracleMain.lean all /tmp/fir-wasm-corpus
node run-artifacts.mjs /tmp/fir-wasm-corpus
```

To compile a Lean source declaration through the real final-impure LCNF
pipeline and emit it directly, import the command after the declaration is
available. Closed declarations need no invocation clause:

```lean
import Fir.Wasm.Emit.Command

def answer : UInt64 := 42

#fir_wasm_emit answer to "answer.wasm"
```

Parameterized declarations record one checked semantic invocation alongside
the reusable module. The module's parameter ABI is the argument schema:

```lean
def idUSize (value : USize) : USize := value

#fir_wasm_emit idUSize with [usize(42)] to "id-usize.wasm"
```

Consumers that will supply every argument at runtime can emit the reusable
module without attaching a sample invocation:

```lean
#fir_wasm_emit_module idUSize to "id-usize-module.wasm"
```

Its JSON descriptor contains only `sourceEntry`, exported `entry`, `params`,
`result`, and the exact semantic-host `imports`. It deliberately has no
`fixture`, `arguments`, or `initialRuntime`; those remain invocation-manifest
fields for reproducible corpus runs. Module-only and invocation-bearing
emission produce identical `.wasm` and `.lcnf` files.

The command writes `answer.wasm`, the Node-compatible ABI manifest
`answer.wasm.json`, and the captured final-impure program
`answer.wasm.lcnf`. Invocation arguments are checked against the ABI kinds
derived from the compiled entry; changing them changes only the manifest, not
the module or captured LCNF. The command accepts `erased`, `tagged(n)`,
`uint8(n)`, `uint16(n)`, `uint32(n)`, `uint64(n)`, and `usize(n)` arguments,
plus `string("…")` and `natList([…])`, with range and schema checks before
compilation. Join-point-bearing source programs remain an explicit fragment
follow-up even when their individual runtime operations are supported.

The lane-local source fixture executes compiler-produced identity declarations
for `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` at their boundary values.
The Node runner derives every physical argument from the manifest and
normalizes signed WebAssembly `i32` results back to the declared unsigned
source width before comparison.
The source checks additionally execute Lean 4.32's compiler-produced small
`Nat` literal, reconstruct a Unicode string and a list containing a natural
above the tagged-immediate range, then execute the list classifier through the
semantic `getTag` import. The natural-literal regression emits the captured
`tagged` binding without rewriting its final-impure types and returns `42` in
Node/V8.

The `source-pretty-format` fixture is the first standard-library algorithm in
this lane. It expands a monomorphic `Std.Format.prettyM` facade beside the
source entry, recursively internalizes compiler-visible helper declarations,
and exports the raw semantic ABI

```text
Format(tobject) × Nat(tobject) × Nat(tobject) × Nat(tobject) → String(object)
```

JavaScript therefore supplies ordinary Lean runtime handles for the format,
page width, indentation, and starting column; there is no second format AST or
high-level adapter. The fixture builds the normal `Format.text`,
`Format.nest`, `Format.line`, and `Format.append` heap graph and compares V8's
`"hello\n  world"` result with native `Std.Format.pretty` at width 12.
A companion invocation of the same Wasm module exercises all eight `Format`
constructors, both flattened and real line breaks, Unicode text, and a newline
embedded inside `Format.text`; V8 again compares with a native Lean oracle.

`call-pretty-format.mjs` demonstrates the consumer boundary using the
invocation-free module descriptor. It creates an empty `SemanticHost`,
instantiates the module once, allocates the eight ordinary Lean 4.32 `Format`
layouts directly in that heap, encodes their raw `tobject` handles, and calls
the same export repeatedly. The small constructor helpers describe only
runtime layout; they do not form a second AST. Run it after artifact generation
with:

```text
node call-pretty-format.mjs _build/source-pretty-format-module.wasm
```

`call-concrete-pretty-format.mjs` keeps that boundary equally low-level while
using the W6 concrete linear-memory representation. JavaScript writes the same
ordinary `Format` constructor layouts and packed bytes through `ConcreteHost`,
passes their physical `tobject` values directly to Wasm, and reads the returned
concrete Lean string. There is no format conversion layer or function-specific
adapter:

```text
node call-concrete-pretty-format.mjs _build/source-pretty-format-module.wasm
```

The first compiler-produced W7 migration runs the identical captured final
LCNF through a checked symbolic link step: every semantic `getTag` call is
rewritten to the Wasm-resident `fir_getTag` helper, one-page memory is defined
and exported, and the concrete client attaches to that memory before creating
raw `Format` values. It retains the other 350 function imports while removing
exactly the one `getTag` import:

```text
node check-resident-pretty-format.mjs \
  _build/source-pretty-format-module.wasm \
  _build/source-pretty-format-resident-get-tag.wasm \
  _build/source-pretty-format-resident-runtime.wasm \
  _build/source-pretty-format-resident-projections.wasm \
  _build/source-pretty-format-resident-closure-projections.wasm \
  _build/source-pretty-format-resident-closure-matches.wasm \
  _build/source-pretty-format-resident-allocator.wasm \
  _build/source-pretty-format-resident-constructors.wasm \
  _build/source-pretty-format-resident-naturals.wasm \
  _build/source-pretty-format-resident-partial-applications.wasm \
  _build/source-pretty-format-resident-setters.wasm \
  _build/source-pretty-format-resident-increments.wasm \
  _build/source-pretty-format-resident-releases.wasm \
  _build/source-pretty-format-trace-resident-releases.wasm \
  _build/source-pretty-format-trace-resident-tag-setters.wasm
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-get-tag.wasm
```

Node and the browser exercise the same native-oracle strings, all eight raw
Lean 4.32 `Format` constructors, Unicode, line behavior, repeated calls, and
module-owned memory. This is an incremental generation result, not the final
zero-function-import W7 artifact or a proof that the linked helper implements
the W6 semantic contract.

The next resident-runtime artifact adds `fir_isShared` without changing final
LCNF, removes the one remaining `isShared` import, and executes through the
same low-level client:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-runtime.wasm
```

The import audit therefore records the monotonic closure
`351 → 350 → 349`: baseline, resident `getTag`, then resident
`getTag + isShared`.

The next retained artifact internalizes the exact eight read projections
reachable from this `prettyM`: four typed object-slot reads and four packed
`UInt8` reads. It preserves final LCNF byte-for-byte, exports each low-level
helper, and reduces function imports from 349 to 341:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-projections.wasm
```

The typed `i32.load8_u` compatibility surface remains independently validated
in the binary encoder and Talos adapter. During this slice,
`FIR-BUG-wasm-none-value-producing-if-encoding` found and fixed a validator
gap: because the binary encoder emits empty-block `if` instructions, the
symbolic validator now rejects reachable arms that change the operand stack.
Projection helpers keep guarded loads stack-neutral through typed locals.
This closes generation readiness for these descriptors, not the later W6
proof that the physical reads implement their semantic contracts.

The closure-capture checkpoint shares helpers by physical slot and result kind.
Compiler-produced call sites still carry their full function, arity, fixed
count, and result descriptor; W6's related-state precondition is responsible
for showing that a successful semantic projection reaches the corresponding
physical slot. The linked artifact removes all 87 `closureProj` imports,
exports twelve low-level helpers, preserves final LCNF, and executes the same
raw `Format` corpus:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-closure-projections.wasm
```

Closure target IDs are now an explicit module contract rather than an
accidental consequence of the remaining import order. Every descriptor carries
the duplicate-free `closureDispatch` array generated in first-use order;
resident linking preserves it even after closure imports disappear, and the
concrete host uses it for allocation. On the proof side, this is the concrete
table to which W6's `RefinementWitness.closureDispatch` must be related. A
future table-layout change therefore remains a shared-contract change rather
than a generation-only rewrite.

Closure capture-layout IDs follow the same rule. The duplicate-free
`closureDescriptors` array is retained independently of runtime imports, so a
resident `partialApply` helper can continue writing the exact descriptor ID
into header word `aux3` after all `partialApply` imports disappear. The
compiler-produced `prettyM` module currently carries 14 rows. Consumers pass
the manifest table to `ConcreteHost`; W6's
`RefinementWitness.closureDescriptors` relates to this exact retained table.

The closure-matching retained audit is
`351 → 350 → 349 → 341 → 254 → 177` function imports. That checkpoint
internalizes all 77 `closureMatches` calls:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-closure-matches.wasm
```

Each exported matcher compares the stable target ID, total arity, and fixed
capture count stored in the closure header. False candidates remain false;
recognized non-heap, misaligned, dead, and non-closure inputs trap. The
remaining 177 imports are 87 partial applications, 23 constructors, 20 cache
initializations, 20 externals, and 27 literal/mutation/reference-count
operations. The later W6 theorem still has to relate these physical comparisons
to semantic `closureMatches` on related states.

The next retained checkpoint keeps that 177-import frontier unchanged and
installs the resident heap owner. Its initialized mutable global starts at
byte 1024; allocation rejects sub-header, unaligned, and overflowing sizes,
grows the module-owned memory by Wasm pages, and returns the prior frontier.
The module also exports a monotone frontier handoff and typed raw stores so
callers can construct values without a high-level adapter:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-allocator.wasm
```

The standalone allocator probe covers invalid inputs, page-crossing growth,
byte-exact stores, Wasm bounds traps, zero imports, Node, Chrome, and Talos
adaptation. The linked `prettyM` still invokes JavaScript for its remaining
runtime families; this checkpoint establishes heap ownership before those
families are internalized.

The next retained checkpoint internalizes all 23 text-frontier constructor
allocations through that allocator, preserves the captured final LCNF, and
reduces imports from 177 to 154:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-constructors.wasm
```

Empty constructors use their tagged immediate representation. Nonempty
constructors zero the complete aligned allocation, install the frozen header,
copy typed fields, and return the raw object word. During the temporary
mixed-runtime phase, `module-client.mjs` synchronizes the monotone resident and
host frontiers at each remaining JavaScript import boundary; this bridge does
not add an ABI and becomes inactive at zero function imports. The full retained
audit is now `351 → 350 → 349 → 341 → 254 → 177 → 177 → 154`.

The following independent checkpoint internalizes the two supported
immediate-Natural literals in text `prettyM`, preserving the captured LCNF and
reducing imports from 154 to 152:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-naturals.wasm
```

Larger naturals remain fail-closed imports until their big-natural allocator
lands. The standalone literal artifact already checks the resident UTF-8
String allocator, but `FIR-BUG-wasm-none-resident-import-location-registry`
requires String linking to wait until its remaining JavaScript consumers are
resident. The styled facade contains two additional event-kind naturals, so
its checkpoint moves from 157 to 153 imports while preserving the exact
native-oracle event stream. The full text audit is now
`351 → 350 → 349 → 341 → 254 → 177 → 177 → 154 → 152`.

The next retained checkpoint internalizes every one of the 87 `partialApply`
operations. Each helper allocates through the resident frontier, zeroes the
complete aligned closure object, writes the stable dispatch and descriptor
IDs plus arity/fixed metadata, copies typed capture slots, and returns the raw
object word:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-partial-applications.wasm
```

The text facade advances from 152 to 65 imports, while the exact-event styled
facade advances from 153 to 66. Both preserve final LCNF and the complete
retained closure tables. The current source closures use only i32 captures;
the standalone fixture additionally checks an i64 `USize` capture. Float
captures fail closed until the resident symbolic surface has typed float
stores. The text audit is now
`351 → 350 → 349 → 341 → 254 → 177 → 177 → 154 → 152 → 65`.

The following checkpoint internalizes all direct constructor mutations:
seven `objectSet` plus four `scalarSet` operations in the text facade, and ten
total setters in the exact-event facade. The checked helpers validate the
resident constructor header and its object/scalar bounds before writing, while
leaving ownership changes to the adjacent explicit reference-count operations:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-setters.wasm
```

Final LCNF and both retained closure tables remain byte-identical. Text
`prettyM` advances from 65 to 54 imports, while styled `prettyM` advances from
66 to 56. The text audit is now
`351 → 350 → 349 → 341 → 254 → 177 → 177 → 154 → 152 → 65 → 54`.

The next independent checkpoint internalizes all four nonrecursive `inc`
operations in each facade. Checked direct immediates and persistent promoted
tags are no-ops; unchecked tagged representations trap; ordinary persistent
objects remain unchanged; and nonpersistent live heap counts are updated only
when the addition does not overflow:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-increments.wasm
```

Final LCNF and both retained closure tables remain byte-identical. Text
`prettyM` advances from 54 to 50 imports, while styled `prettyM` advances from
56 to 52. The text audit is now
`351 → 350 → 349 → 341 → 254 → 177 → 177 → 154 → 152 → 65 → 54 → 50`.

The following checkpoint internalizes the five distinct recursive `dec`
operations plus nonrecursive `delete` in each facade. A shared Wasm helper
marks a count-one parent released before recursively visiting constructor
object slots or the object-like captures selected by the retained closure
descriptor table. Checked immediate and promoted-tag lanes remain no-ops;
unchecked lanes, stale headers, underflow, unknown or mismatched descriptors,
and cycles trap:

```text
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-releases.wasm
```

Final LCNF, closure dispatch, and closure descriptors remain byte-identical.
Text `prettyM` advances from 50 to 44 imports, while styled `prettyM` advances
from 52 to 46. The text audit is now
`351 → 350 → 349 → 341 → 254 → 177 → 177 → 154 → 152 → 65 → 54 → 50 → 44`.

The next checkpoint is deliberately styling-only. Plain-text `prettyM` has no
constructor-tag write and remains at 44 imports. Exact-event `prettyM` has one
fixed `setTag 1` operation; the guarded resident helper removes it, preserves
final LCNF and both closure tables, and advances the styled facade from 46 to
45 imports.

For a reproducible handoff to another agent, `package-pretty-format.sh`
builds the styled facade in `FirWasmPrettyTraceExample.lean` and prepares a
self-contained copy of the current JavaScript-hosted runtime, raw-layout smoke
client, descriptor, final LCNF, checksums, and capability metadata. The
canonical `_build/prettyM-current` symlink is moved only after its immutable
release has passed the checksum and smoke gates:

```text
./package-pretty-format.sh
cd _build/prettyM-current
node smoke.mjs
```

This package is explicitly experimental and unversioned. Its module owns its
memory and allocator and currently has 45 function imports: one more than
the text-only 44-import checkpoint in order to preserve the exact
`MonadPrettyFormat` output/newline/start-tag/end-tags event stream. The plain
rendered `String` remains available as the trace's text projection. Node and
the Chrome Worker decode the resident result constructor directly and compare
the exact event stream with the native Lean 4.32 oracle; zero imports is the
later W7 closure milestone.

The invocation-bearing coverage artifact exercises the same export after its
ordinary `Format` graph has crossed the initial-runtime manifest boundary:

```text
node call-concrete-pretty-format-invocation.mjs \
  _build/source-pretty-format-coverage.wasm
```

`module-client.mjs` is the transport-neutral loading boundary. Its core entry
accepts Wasm bytes, the parsed invocation-free descriptor, and a caller-owned
semantic ABI host; `fetchModuleArtifact` obtains the first two inputs through
the web-standard Fetch API. `node-module-client.mjs` is the small filesystem
wrapper that creates the repository's `SemanticHost`. Both return the raw
exported function and deliberately avoid creating source-language values or a
function-specific API. The caller continues to allocate runtime values in the
host and use `host.encode`/`host.decode` with the descriptor's ABI kinds.

For a fetch-capable JavaScript environment with a compatible semantic host:

```js
const { manifest, entry } = await fetchModuleArtifact("pretty.wasm", { host });
const physicalResult = entry(...physicalArguments);
const result = host.decode(manifest.result, physicalResult);
```

The shipped semantic host and Format external registry are also free of Node
built-ins. `fetch-pretty-format.mjs` therefore runs the same raw-layout and
cache-reuse checks as the Node client inside a module Web Worker. The permanent
headless-browser/worker regression is opt-in so the normal artifact lane does
not require a proprietary browser package:

```text
./browser-check.sh google-chrome
FIR_BROWSER=google-chrome ./check.sh
```

The initial browser validation used Google Chrome 150.0.7871.114. Chrome is
not added to the repository's required tooling; any compatible headless
Chromium-family executable may be passed explicitly.

The browser lane also consumes the validation harness's shared semantic-Wasm
product bundle rather than rebuilding or renaming case artifacts. The Node
adapter and browser Worker share `scripts/wasm_validation_case.mjs` for ABI
argument checking, module import/export checking, result normalization, and
effect projection. The Worker fetches `matrix.json`, `corpus.json`, and each
case-bound manifest/module, verifies every product digest with Web Crypto,
executes every selected case, and compares each observation with the
canonical Node/V8 result from that same run. Generate the products and run the
standalone browser check with:

```text
make -C ../../.. validate-v8
./browser-validation-check.sh google-chrome
```

Setting `FIR_BROWSER` on `check.sh` runs both the reusable `prettyM` Worker and
the complete shared-product Worker. It also materializes the live-oracle
artifact corpus under `_build`, then runs the same 43 concrete artifacts, one
default external rejection, and one expected failure used by Node through a
third Worker. That Worker also executes the concrete initial-runtime
complete 13-probe compiler source inventory—including both initial-runtime
`prettyM` invocations and the invocation-free raw-layout module—through the
same concrete checkers used by Node. The shared-product Worker independently
executes the 70 non-`ByteArray` products through the concrete host after their
semantic executions and verifies the exact 33-case blocker inventory.

A repository-local alternate validation directory can be supplied as the
second argument for focused semantic-product runs. After a browser-enabled
artifact check, the concrete Worker can be rerun directly with:

```text
./browser-concrete-check.sh google-chrome _build/concrete-corpus
```

The client also retains the focused expected-failure regression for
`FIR-BUG-impure-none-cached-heap-persistence`. A longer standalone group reads
a cached heap `SpaceResult` after shared FIR cache semantics have allowed it to
be reused and released. Fixing that requires one coordinated persistence
transition in the FIR interpreter, semantic host, and W6 refinement; this lane
does not hide the discrepancy with a V8-only repair.

Lean 4.32 initially exposes 23 helper declarations outside the raw local
closure because primitives and compiler-generated specializations are emitted
as external LCNF declarations. Recursive source internalization leaves 20
actual declaration-level runtime primitives. The manifest contains more
imports because semantic heap, closure, and call operations receive distinct
metadata-bearing import identities; those are instances of the frozen
semantic runtime ABI, not additional source helpers. The unreachable panic
fallback remains a trapping import and is asserted absent from the successful
execution trace.

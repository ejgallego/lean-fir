# FIR Wasm artifact lane

This package turns the supported W3--W5 semantic FIR corpus into deterministic WebAssembly 1.0
binary artifacts, then runs those artifacts in Node's standard `WebAssembly` engine with
a small semantic FIR host.

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

This builds the Lean emitter, runs the semantic oracle through Lean, emits the corpus and oracle
results twice, byte-compares all outputs, validates and instantiates every module in Node,
executes `main`, and compares the V8 observation with FIR. It requires Lean 4.32, the
worktree-local Talos setup, and Node; no external WAT or WebAssembly CLI is required. The
oracle uses `lean --run` so a fresh worktree does not native-compile the full upstream Wasm
semantics just to check this corpus.

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

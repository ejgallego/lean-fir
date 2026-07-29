# Current `Std.Format.prettyM` Wasm package

This folder is a reproducible handoff of the current, tested FIR artifact. The
compiler-produced Wasm module uses the concrete `wasm32-lean64`
representation, owns and exports its linear memory, and carries the first W7
resident heap boundary. The module has zero imports: JavaScript constructs and
decodes raw Lean values but implements no runtime operation used by `prettyM`.

The exported raw boundary is:

```text
Format(tobject) × Nat(tobject) × Nat(tobject) × Nat(tobject)
  → PrettyTrace(object)

PrettyTrace := { text : String, eventsRev : List PrettyEvent }
PrettyEvent := { kind : Nat, text : String, value : Nat }
```

`prettyM-browser-adapter.mjs` is the production-oriented browser boundary.
It accepts a compact, versioned JavaScript description of `Std.Format`, then
constructs ordinary Lean 4.32 `Format` heap objects directly in the exported
module memory. It does not implement a second pretty printer or runtime.
Consumers that need the compiler-facing boundary may still call the raw export
and allocator operations directly.
`eventsRev` preserves the complete reverse-chronological
`MonadPrettyFormat` protocol: text output, newlines, tag starts, and tag ends.
The `text` field is the plain `String` projection for consumers that
intentionally do not observe styling.

The underlying Wasm boundary remains experimental and unversioned:
`BUILD.json` keeps its ABI version at `null`. The browser adapter has its own
versioned API, input-layout, and ownership capabilities so a consumer can
negotiate that smaller surface without treating every raw runtime detail as
stable.

## Browser adapter

The public input layout is
`lean-4.32-Std.Format.compact/v1`. Its TypeScript-style shape is:

```ts
type NatInput = bigint | number /* safe integer */ | string /* canonical decimal */;
type IntInput = bigint | number /* safe integer */ | string /* canonical decimal */;

type Format =
  | { kind: "nil" }
  | { kind: "line" }
  | { kind: "align", force: boolean }
  | { kind: "text", text: string }
  | { kind: "nest", indent: IntInput, body: Format }
  | { kind: "append", left: Format, right: Format }
  | { kind: "group", body: Format, behavior?: "allOrNone" | "fill" | 0 | 1 }
  | { kind: "tag", tag: NatInput, body: Format };
```

Use it from a browser Window or Worker:

```js
import {
  PrettyFormat as F,
  fetchPrettyMAdapter,
} from "./prettyM-browser-adapter.mjs";

const prettyM = await fetchPrettyMAdapter(
  new URL("./prettyM.wasm", import.meta.url),
);
const result = prettyM.render({
  format: F.group(F.append(F.text("hello"), F.line())),
  width: 80,
  indent: 0,
  column: 0,
});
console.log(result.trace.text);
console.log(result.trace.events); // exact styling protocol
console.log(result.timings);
console.log(result.memory);
```

`prepare`, `execute`, and `decode` are also public for consumers that need
phase-separated timings. `render` performs those three phases immediately.
Startup timings (`fetchMs`, `compileMs`, and `instantiateMs`) are exposed as
`adapter.startupTimings`; each result reports normalization, resident
allocation, raw encoding, execution, decoding, and aggregate timings.

The adapter borrows the JavaScript input and never mutates it. Each call
encodes a fresh owned Lean graph and transfers it to the entry point. Returned
raw addresses are not exposed: `decode` copies the text and exact event stream
into JavaScript values. Module memory is a monotone bump arena for the lifetime
of the adapter instance. The adapter reads and validates the resident frontier
before and after every phase, and uses one `fir_heap_alloc` call for the entire
input graph. Discard the adapter instance to reclaim its arena.

## Build the package

From the repository root:

```sh
integration/talos/artifact/package-pretty-format.sh
```

The canonical package path is:

```text
integration/talos/artifact/_build/prettyM-current/
```

Each invocation first builds and tests a complete immutable release, then
atomically moves the `prettyM-current` symlink to it. Readers therefore see
either the previous complete package or the new complete package, never a
mixture of their files. The sibling `prettyM-current-releases/` directory
contains the symlink targets.

An alternate canonical output path can be passed as the first argument.
If the source artifact has already been generated, `--no-build` re-packages
and tests it without rerunning Lean:

```sh
integration/talos/artifact/package-pretty-format.sh --no-build
```

## Test the prepared package

```sh
cd integration/talos/artifact/_build/prettyM-current
node smoke.mjs
```

The expected result is:

```text
PASS concrete styled prettyM trace (Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw)
```

`SHA256SUMS` authenticates the capability metadata, README, Wasm module,
descriptor, final LCNF capture, smoke client, and copied runtime sources.
`BUILD.json` records the source commit and dirty state, raw boundary, artifact
size and digest, measured capabilities, and exact test command.

## Runtime boundary

`prettyM.wasm` is the zero-function-import W7 artifact. It owns a
`WebAssembly.Memory`,
starts its private frontier at byte 1024, and exports low-level
`fir_heap_frontier`, `fir_heap_set_frontier`, `fir_heap_alloc`, and typed raw
store operations. The accompanying `runtime/` tree is an allocation and
decoding client only; it supplies no imported function to Wasm.
All 27 constructor-allocation operations, all four immediate-Natural literal
operations, all 87 closure-allocation operations, all ten direct
constructor-setter operations, and all four nonrecursive reference-count
increments in the styled artifact are resident in Wasm. All five distinct
recursive decrement operations and nonrecursive delete are resident as well;
constructor children and statically object-like closure captures are released
inside the module. The styling-only fixed constructor-tag mutation is resident
as well. All 21 lazy-cache publication operations are resident too: their
reachable constructor and closure graphs are marked persistent recursively in
Wasm while the compiler-generated module globals continue to own the cached
physical lanes. The ten Nat/Int operations reachable from `prettyM` are
resident for canonical immediate, promoted one-limb, and arbitrary multi-limb
values, including signed representation transitions and carry/borrow across
limbs. All eight UTF-8 String operations reachable from `prettyM` and its four
String literals are resident as well. The two failure-only
panic/inhabited fallbacks are resident unconditional traps, preserving the
previous fail-closed behavior without a host import.

The smoke clients prepare ordinary Lean values directly in the exported
memory, advance the monotone resident frontier, decode the raw trace graph, and
check both rendered text and exact tag boundaries against an event oracle also
guarded by native Lean 4.32. The browser-adapter smoke reuses the same compact
input across two calls, checks a multi-limb width, verifies one resident bulk
allocation per input, and checks frontier synchronization. Keeping this
package separate provides a coherent integration snapshot while allocation
families move behind the resident boundary; only the explicitly versioned
adapter capabilities are intended for consumer negotiation.

The module descriptor also carries the retained `closureDispatch` and
`closureDescriptors` tables. They assign the target and capture-layout IDs
stored in closure header words `aux0` and `aux3`, respectively. Consumers pass
both tables unchanged to `ConcreteHost`; they remain available after their
introducing closure operations are internalized and disappear from the import
list.

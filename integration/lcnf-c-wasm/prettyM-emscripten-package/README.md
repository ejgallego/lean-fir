# LLVM-backed C/Emscripten `Std.Format.prettyM` package

This is the compiler-native counterpart to the separate FIR-native `prettyM`
package. Its build route is:

```text
Lean final LCNF -> generated C -> Emscripten/LLVM Wasm
```

In this guide, **the LLVM artifact** means this C/Emscripten bundle. It is not
the FIR-native raw-Wasm package under `integration/talos/artifact`; the two
packages expose the same logical JavaScript request and result but have
different loaders and raw Wasm ABIs.

The package intentionally retains the Emscripten ES-module loader, pinned full
Lean runtime, and threaded host contract. It does not share the FIR-native
package's zero-import raw Lean-object ABI. Both packages instead expose the
same browser-level contract:

```text
fir.prettyM.browser/v1
lean-4.33-Std.Format.compact/v1

render({ format, width, indent?, column? })
  -> { trace: { text, events }, timings, memory }
```

## Build and hand off the package

From the FIR repository root, build and run the exact differential test:

```sh
integration/lcnf-c-wasm/package-prettyM-emscripten.sh
```

The default package directory is
`integration/lcnf-c-wasm/_build/prettyM-emscripten-current/`. A client only
needs these files from that directory:

```text
prettyM.manifest.json
prettyM.mjs
prettyM.wasm
emscripten-loader.mjs
prettyM-emscripten-adapter.mjs
SHA256SUMS
README.md
```

Keep their filenames and relative locations unchanged. The manifest names the
ES module and Wasm file relative to itself, and the loader verifies both files'
lengths and SHA-256 digests before initializing the Lean runtime. The client
does not need Lean, Lake, LLVM, Emscripten, or the FIR repository.

The producer can choose a different package directory:

```sh
integration/lcnf-c-wasm/package-prettyM-emscripten.sh /tmp/fir-prettyM
```

Verify the handoff before publishing it:

```sh
cd /tmp/fir-prettyM
sha256sum -c SHA256SUMS
```

## Node client

Place the following `client.mjs` beside the packaged files, then run it with a
modern Node release using `node client.mjs`:

```js
import {
  loadEmscriptenPrettyMAdapter,
  PrettyFormat as F,
} from "./prettyM-emscripten-adapter.mjs";

const prettyM = await loadEmscriptenPrettyMAdapter(
  new URL("./prettyM.manifest.json", import.meta.url),
);
try {
  const format = F.group(
    F.append(F.text("hello"), F.append(F.line(), F.text("world"))),
  );
  const result = prettyM.render({ format, width: 80 });
  console.log(result.trace.text);   // "hello world"
  console.log(result.trace.events); // exact output/newline/tag protocol
} finally {
  prettyM.dispose();
}
```

Loading is asynchronous because it reads, authenticates, compiles, and
initializes the artifact. `render` is synchronous and not reentrant. Reuse one
adapter for sequential renders, then call `dispose()` exactly when the client
is finished with it. Rendering after disposal is rejected.

## Browser client

The same ES-module import and client code work in a browser Window or Worker.
Deploy the package through HTTP(S), not `file:`, and serve the application as a
cross-origin-isolated page because the optimized artifact uses Emscripten
threads. At minimum, the document response needs:

```http
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
```

Serve same-origin package files, or give cross-origin files an appropriate
CORS or `Cross-Origin-Resource-Policy` response. Use conventional MIME types,
including `application/wasm` for `.wasm`, JavaScript for `.mjs`, and
`application/json` for the manifest. Before loading the package, the
application can fail early with:

```js
if (!globalThis.crossOriginIsolated) {
  throw new Error("the FIR LLVM artifact requires cross-origin isolation");
}
```

## Request and result contract

`PrettyFormat` constructs the versioned
`lean-4.33-Std.Format.compact/v1` input:

```ts
type NatInput = bigint | number /* safe, nonnegative integer */
  | string /* canonical unsigned decimal */;
type IntInput = bigint | number /* safe integer */
  | string /* canonical signed decimal */;

type Format =
  | { kind: "nil" }
  | { kind: "line" }
  | { kind: "align", force: boolean }
  | { kind: "text", text: string }
  | { kind: "nest", indent: IntInput, body: Format }
  | { kind: "append", left: Format, right: Format }
  | { kind: "group", body: Format,
      behavior?: "allOrNone" | "fill" | 0 | 1 }
  | { kind: "tag", tag: NatInput, body: Format };
```

`width`, `indent`, and `column` are `NatInput`; omitted `indent` and `column`
default to zero. Use `bigint` or a canonical decimal string when a value is
outside JavaScript's safe integer range. Format graphs must be acyclic.

`result.trace.text` is the plain rendered string. `result.trace.events` is the
chronological `MonadPrettyFormat` event stream:

| `kind` | Meaning | Payload |
| --- | --- | --- |
| `0` | output | `text`; `value` is `0n` |
| `1` | newline | `value` is the following indentation |
| `2` | start tag | `value` is the arbitrary-precision tag |
| `3` | end tags | `value` is the number of tags ended |

Every event `value` is a JavaScript `bigint`. `result.timings` separates wire
encoding, execution, and decoding. `result.memory` reports request and response
sizes, format-node count, and Emscripten heap sizes; these are diagnostics, not
stable addresses.

Applications can lower the default request limits when creating the adapter:

```js
const prettyM = await loadEmscriptenPrettyMAdapter(manifestURL, {
  maximumNodes: 100_000,
  maximumBytes: 16 * 1024 * 1024,
});
```

The package maximum is 1,000,000 format nodes and 64 MiB per encoded request.
Input validation, loader verification, initialization, and Lean-side failures
are reported as JavaScript exceptions.

## Boundary and build properties

The adapter validates the compact format tree, encodes one
`fir.prettyM.emscripten-wire/v1` request, transfers it through `HEAPU8`, and
copies one response back. The C bridge owns its buffers. The wire is private
to this package: clients should use `render`, not the five raw bridge exports.

The Lean entry point reconstructs the ordinary Lean 4.33 `Std.Format`, calls
the real monomorphic `Std.Format.prettyM`, and records the full output,
newline, start-tag, and end-tags protocol. Natural and integer inputs use
canonical arbitrary-precision 32-bit limbs.

Packaging loads this artifact and the independent FIR-native package, sends
identical compact requests to both, and compares exact traces. Producers can
set `FIR_PRETTY_M_NATIVE_PACKAGE` to compare against another FIR-native
package.

The generated Lean C, bridge C, and final Wasm are compiled with `-O3`,
`-DNDEBUG`, LTO, hidden visibility, section garbage collection, frame-pointer
omission, and exact floating-point settings. The manifest records the flags,
toolchain pins, source inventory, public exports, artifact sizes, and SHA-256
digests. `SHA256SUMS` also covers the packaged loader, adapter, and this file.

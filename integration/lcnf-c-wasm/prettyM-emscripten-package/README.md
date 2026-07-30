# C/Emscripten `Std.Format.prettyM` package

This is the compiler-native counterpart to the separate FIR-native `prettyM`
package. Its build route is:

```text
Lean final LCNF -> generated C -> Emscripten/LLVM Wasm
```

The package intentionally retains the Emscripten ES-module loader, pinned full
Lean runtime, and threaded host contract. It does not share the FIR-native
package's zero-import raw Lean-object ABI. Both packages instead expose the
same browser-level contract:

```text
fir.prettyM.browser/v1
lean-4.32-Std.Format.compact/v1

render({ format, width, indent?, column? })
  -> { trace: { text, events }, timings, memory }
```

Use it from Node or a cross-origin-isolated browser:

```js
import {
  loadEmscriptenPrettyMAdapter,
  PrettyFormat as F,
} from "./prettyM-emscripten-adapter.mjs";

const prettyM = await loadEmscriptenPrettyMAdapter(
  new URL("./prettyM.manifest.json", import.meta.url),
);
const result = prettyM.render({
  format: F.group(F.append(F.text("hello"), F.line())),
  width: 80,
});
console.log(result.trace.text);
console.log(result.trace.events);
prettyM.dispose();
```

The adapter validates the compact format tree, encodes one
`fir.prettyM.emscripten-wire/v1` request, transfers it through `HEAPU8`, and
copies one response back. The C bridge owns its buffers. The wire is private
to this package: clients should use `render`, not the five raw bridge exports.

The Lean entry point reconstructs the ordinary Lean 4.32 `Std.Format`, calls
the real monomorphic `Std.Format.prettyM`, and records the full output,
newline, start-tag, and end-tags protocol. Natural and integer inputs use
canonical arbitrary-precision 32-bit limbs.

Build and test this package from the repository root:

```sh
integration/lcnf-c-wasm/package-prettyM-emscripten.sh
```

The default output is
`integration/lcnf-c-wasm/_build/prettyM-emscripten-current/`.
The check loads this package and the independent FIR-native package, sends
identical compact requests to both, and compares exact traces. Set
`FIR_PRETTY_M_NATIVE_PACKAGE` to test against another FIR-native package.

The generated Lean C, bridge C, and final Wasm are compiled with `-O3`,
`-DNDEBUG`, LTO, hidden visibility, section garbage collection, frame-pointer
omission, and exact floating-point settings. The manifest records the flags,
toolchain pins, source inventory, public exports, artifact sizes, and SHA-256
digests. `SHA256SUMS` also covers the packaged loader, adapter, and this file.

# LLVM-backed complete PrettyM HTML package

This package compiles the unmodified
`VersoSlides.Pretty.formatHtmlForRuntime` surface through Lean final LCNF,
generated C, and Emscripten/LLVM Wasm. It accepts the same compact Lean 4.32
`Std.Format`, sparse tagged annotations, width, indent, and initial column as
the FIR-native and VIR complete-HTML candidates.

The browser-level endpoint is:

```text
fir.prettyM.html.emscripten.browser/v1
compact format + tagged annotations -> verso-token-html/v1
```

The returned string includes layout, annotation resolution, escaping, and
span construction. DOM parsing and commit remain outside the artifact. The
adapter reports encode, execute, and decode timings separately.

Build and run the exact differential gate from the FIR repository root:

```sh
VERSO_ROOT=/path/to/clean/verso \
  integration/lcnf-c-wasm/package-prettyM-html-emscripten.sh
```

The package is self-contained at runtime. Serve it from a cross-origin
isolated page because the Emscripten module uses threads. `SHA256SUMS` covers
the loader, shared compact-format codec, HTML adapter, manifest, module, Wasm,
and this README.

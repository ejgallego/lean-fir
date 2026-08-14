# Wasm function evidence

`function-index.mjs` binds optimized Wasm function indices to a release
artifact. It does not infer final indices by zipping a pre-link declaration
inventory with a post-link binary: Binaryen can delete, inline, synthesize, and
reorder functions.

The capture protocol is deliberately split around the existing linker:

1. `prepare` replaces debug function names in a temporary input with unique
   absolute-index tokens and writes their Lean identities to a capture
   manifest. These names exist only in identity-carrying build intermediates.
2. After every merging, DCE, or ordering stage, `restamp` captures the stage's
   old-to-new function map in the manifest and replaces temporary names with
   the new absolute-index tokens.
3. The final `wasm-opt` invocation is made through `optimize`, which adds
   `--print-function-map`; the normal stripped output remains the release
   artifact.
4. `wasm-opt --print-call-graph` reads that final artifact without optimization.
   Binaryen may re-encode the discarded output copy, so the tool verifies its
   final stripped function map and never substitutes that copy for the release
   bytes. In that map imports are named `fimport$N`, while definitions are
   named by a zero-based ordinal that excludes imports.
5. `finalize` combines the captured map and graph with binary body sizes and
   exports, then binds the result to the release SHA-256.

Functions introduced by the linker or optimizer, or functions whose temporary
identity does not survive, remain explicitly classified as
`optimizer-or-linked-runtime`. The sidecar never guesses a Lean name.

When import/export minification is enabled, Binaryen writes rename diagnostics
beside `--print-function-map`. The parser deliberately consumes only numeric
`index:name` rows.

Multi-module link steps must preserve the temporary name section (for Binaryen,
pass `--debuginfo` to `wasm-merge` and `wasm-metadce`). The final `optimize`
step strips names from the release artifact.

## Commands

```text
node tooling/wasm/function-index.mjs prepare \
  --wasm app.wasm --inventory app.wasm.inventory.json \
  --named-wasm app.named.wasm --capture app.capture.json

node tooling/wasm/function-index.mjs restamp \
  --binaryen-dir /path/to/binaryen/bin --wasm app.merged.wasm \
  --capture app.capture.json --wasm-opt-args app.wasm-opt-args.json \
  --named-wasm app.merged.named.wasm --output app.merged.capture.json

node tooling/wasm/function-index.mjs finalize \
  --wasm app.release.wasm --capture app.capture.json \
  --function-map app.function-map.txt --call-graph app.call-graph.dot \
  --output app.release.wasm.functions.json

node tooling/wasm/function-index.mjs verify \
  --wasm app.release.wasm --sidecar app.release.wasm.functions.json

node tooling/wasm/function-index.mjs inspect \
  --wasm app.release.wasm --sidecar app.release.wasm.functions.json \
  --function 17
```

`optimize` can replace a linker's final `wasm-opt` invocation without owning
the linker's flags. The JSON file is an array containing those exact arguments:

```text
node tooling/wasm/function-index.mjs optimize \
  --binaryen-dir /path/to/binaryen/bin --input app.private.wasm \
  --wasm app.release.wasm --capture app.capture.json \
  --wasm-opt-args app.wasm-opt-args.json \
  --output app.release.wasm.functions.json
```

The focused Binaryen test also checks that temporary identities do not change
the stripped release bytes:

```text
FIR_BINARYEN_DIR=/path/to/binaryen/bin \
  node --test tooling/wasm/function-index.test.mjs
```

The representative multi-module check used the Illuminate selection-player
artifact from FIR `8c5fc9f13fd871f1453f0a6e2fc476c125adc3e5`. The restamped capture reproduced
the accepted 35,240-byte artifact at SHA-256
`4f538ee895c3c730c1cd237d52d0d0f93101af758d732b3c1d0c161c50c97e83`
exactly. Its final 84 functions comprise 15 retained Lean-source functions,
66 resident helpers, and three deliberately unattributed linked-math
functions. This check exercises `wasm-merge`, `wasm-metadce`, and the release
`wasm-opt -O3` path, rather than only a direct single-module optimization.

This is artifact-local evidence. Browser campaign selection and comparative
presentation remain in VIR; application corpora and semantic oracles remain in
their client repositories.

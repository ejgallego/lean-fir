# Verso complete-HTML `prettyM` package

This integration compiles the real
`VersoSlides.Pretty.formatHtmlForRuntime` final-LCNF closure and links the
complete Lean runtime frontier into a zero-import Wasm module. The source
implementation is neither copied nor adapted inside FIR.

The browser/Node adapter accepts the compact Lean 4.32 `Std.Format` object used
by FIR's other `prettyM` packages plus an array of
`{ tag, annotation: { cssClass, binding } }` values. It returns a copied,
escaped HTML String whose spans implement Verso's `verso-token-html/v1`
contract. No raw Wasm address escapes the adapter.

## Source and capture

The exact clean Verso revision and source digest are pinned in
`verso-source.json`. Point `.verso` at that checkout, or set `VERSO_ROOT`:

```sh
ln -s /absolute/path/to/clean/verso .verso
```

FIR asks Lean for one captured final-LCNF unit rooted at the public entry. This
is deliberately slower than replaying module-wise fragments, but it preserves
the specializations produced by the source compilation and reduces the
external frontier to generic runtime operations. `closure-contract.json`
ratchets the complete declaration, helper, size, and inventory digests.

## Complete gate and publication

```sh
VERSO_ROOT=/absolute/path/to/clean/verso bash check.sh
```

The gate publishes twice to prove deterministic identity, verifies every
checksum, compares eight Wasm results with the native Lean entry, checks
escaping and nested annotations, exercises memory growth and repeated calls,
and runs the source repository's package validator. Set
`FIR_BROWSER=google-chrome` to add the real browser fetch/compile/render check.

Immutable packages live under `_build/verso-html-packages/`.
`_build/verso-html-current` is atomically updated to the accepted package.
Each package contains:

- `prettyM.wasm` and `prettyM.wasm.json`;
- `prettyM-browser-adapter.mjs`;
- `BUILD.json` and `SHA256SUMS`;
- `smoke.mjs`.

The module owns its memory, has zero imports, and exports only the structured
entry, four arena functions, and memory. Inputs are fresh transferred Lean
graphs. Output HTML is copied before it is returned. The arena is monotonic for
the instance lifetime, so consumers should use fresh instances for bounded
batches when measuring memory.

## Known performance follow-up

The current Verso source escapes HTML through character-at-a-time immutable
`String.push`. The resident implementation follows Lean's generic semantics,
which makes long escaped output quadratic in allocation volume in the monotonic
Wasm arena. The package gate therefore uses a bounded memory-growth case. The
separate source-owner throughput acceptance should replace the escape loop with
a builder/chunk strategy before reinstating the >=1 MiB headline case.

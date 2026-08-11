# Verso Flat `prettyM` package

This integration compiles the real
`VersoSlides.Pretty.formatRenderedForRuntime` final-LCNF closure and links its
complete runtime into a zero-import Wasm module. It is a separate Flat-output
experiment; it does not replace the established FIR `PrettyTrace` control.

The browser adapter accepts the same compact Lean 4.33 `Std.Format` input as
the control package. Wasm returns `{ text, events }`, where event offsets are
UTF-8 byte offsets and event kinds are start tag `0`, end-tags `1`, and
unstyled newline `2`.

## Source view

The build reads `VersoSlides/Pretty.lean` from a clean checkout without using
that checkout's `.lake`:

```sh
ln -s /absolute/path/to/clean/verso .verso
```

The exact revision and file digest are pinned in `verso-source.json`. A null
`remoteRef` deliberately marks packages provisional until the Verso owner
publishes the clean capture refactor; no source implementation is vendored or
copied into FIR.

## Complete check

```sh
VERSO_ROOT=/absolute/path/to/clean/verso bash check.sh
```

The gate builds the native examples, publishes twice to prove deterministic
identity, verifies every checksum, runs the package smoke test, compares nine
Wasm results with the native Lean definition, and covers 1 MiB UTF-8 output,
the 2047-node balanced tree, 256 grouped breaks, and 32 repeated calls. If the
Verso package validator is present in the source checkout, the gate runs it as
well.

Set `FIR_BROWSER=google-chrome` (or another Chromium-compatible executable) to
add the real browser fetch/compile/instantiate/render smoke test.

During source-owner coordination only,
`VERSO_ALLOW_UNPUBLISHED_SOURCE=1` permits this gate to exercise a clean local
commit while retaining `provisional: true` in `BUILD.json`. Accepted
publication never sets that override; it requires the pinned commit to be
reachable from `remoteRef`.

The immutable packages live under `_build/verso-flat-packages/` and
`_build/verso-flat-current` is atomically replaced with a symlink to the
current package.

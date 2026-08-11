# Verso complete-HTML source probe

This project captures the real
`VersoSlides.Pretty.formatHtmlForRuntime` entry through FIR's module-wise
postponed final-LCNF path. It does not copy the Verso implementation or consume
Verso build products.

The source boundary is healthy: the exact published `VersoSlides.Pretty`
module rebuilds with `compiler.postponeCompile=true`, and the FIR compile
surface elaborates without diagnostics. Resident linking is currently blocked
by `FIR-BUG-impure-none-generated-external-source-ancestor`: the HTML entry
still reaches generated declarations in precompiled Lean core modules through
`StateT`, `String.join`, and `String.replace`.

Reproduce the accepted diagnostic with a clean checkout of the source commit
recorded in `verso-source.json`:

```sh
ln -s /absolute/path/to/clean/verso-checkout .verso
lake --keep-toolchain --reconfigure build VersoFirHtml.Compile
lake --keep-toolchain env lean Emit.lean
```

The second command intentionally fails closed rather than producing a package
with host fallbacks. At the recorded source revision it emits a 32,407-byte
base module with 498 FIR runtime operations and 52 Lean externals, then reports
the first incomplete resident family at `String.Internal.append`.

Publication resumes after the source entry adopts an explicit specialized HTML
state monad, a local chunk join, and source-local escaping. The intended public
surface remains `fir-prettyM-package-metadata-v2` with browser API
`fir.prettyM.html.browser/v1`, module-owned memory, and zero imports.

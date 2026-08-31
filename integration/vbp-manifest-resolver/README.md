# FIR-native VBP manifest resolver

This integration compiles the real
`VersoBlueprint.Runtime.ManifestResolver.resolveBatchJson : String → String`
root from VBP revision `1af64db22340823e4d295d7613f676e6ff84246a`
under Lean `v4.34.0-rc2`. The generated module owns its memory and has zero
imports. No Blueprint component, renderer, filesystem, RPC, or browser API is
part of the closure.

The browser/Node adapter exposes the provider-compatible synchronous operation:

```js
const outputJson = adapter.invoke(
  "VersoBlueprint.Runtime.ManifestResolver.resolveBatchJson",
  [inputJson],
);
```

It transfers a fresh Lean UTF-8 String, copies the result back to JavaScript,
and rewinds the module-owned scratch arena after every call. No raw address
escapes. `adapter.lastCall` reports encode, execute, decode, rewind, and memory
frontier diagnostics. `dispose()` invalidates the adapter and releases the
instance to JavaScript garbage collection.

## Exact build and smoke gate

Point `VBP_ROOT` at a clean checkout of the pinned revision, or use the default
clean source view under the FIR worktree:

```sh
VBP_ROOT=/absolute/path/to/clean/verso-blueprint bash check.sh
```

The gate builds FIR itself in a clean worktree-local source archive so Lean
4.34 products never enter W7's Lean 4.33 `.lake`. It regenerates twice, checks
immutable identity, verifies `SHA256SUMS`, and runs all 11 fixture requests,
five malformed-manifest cases, malformed JSON, Unicode transport, repeated
calls, deterministic timing injection, disposal, and flat post-call frontier
checks.

Immutable local packages are published below
`_build/vbp-manifest-resolver-packages/`; the atomic
`_build/vbp-manifest-resolver-current` symlink names the current package.

# Immutable package utilities

`immutable-package.mjs` contains the narrow publication behavior shared by
accepted FIR browser packages:

- generate and verify an exact ordered `SHA256SUMS` inventory of regular files;
- stage a complete directory before exposing it;
- reject reuse of one package identity with different bytes;
- rename a new immutable directory atomically; and
- atomically replace the optional `*-current` symlink.

Package-specific compilation, metadata, adapters, source provenance, oracle
comparisons, memory limits, and browser tests remain in each integration. The
shared function accepts only a package ID, an ordered file inventory, a staging
callback, and an optional current-link path; it is not a build framework.

`verified-package.mjs` is the matching consumer-side boundary. A small package
policy names the exact checksummed payload, BUILD schema and capability values,
Wasm file, imports, exports, ownership, and packaged smoke. The verifier checks
those declarations against the actual module. The installer copies only a
verified package into a staging directory beside a fresh caller-owned output,
smokes it before and after the atomic rename, and removes a rejected output.
Application semantics and workload-specific memory limits are deliberately not
part of this shared surface.

`source-package.mjs` projects a verified package into the optional
`browser-benchmarks/source-package/v1` discovery vocabulary. It normalizes
provenance, producer and adapter identity, verifier inputs, production versus
diagnostic operations, public phase names, and ownership. See
`SOURCE_PACKAGE.md`. The current coordination draft is returned in memory and
does not change immutable package bytes or identities.

Accepted producers can pass a `validate(staging)` callback to
`publishImmutablePackage`. It runs after the exact checksum manifest exists but
before either the immutable directory or its current symlink is exposed.

`postponed-source-view.mjs` builds only the private `.olean` replay surface for
one explicitly named source module. It does not ask Lean to finish unrelated
native IR; consumers prepend the returned path only while running FIR capture.

Run the focused contract with:

```sh
node --test integration/package-tools/*.test.mjs
```

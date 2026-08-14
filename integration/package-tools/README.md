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

`postponed-source-view.mjs` builds only the private `.olean` replay surface for
one explicitly named source module. It does not ask Lean to finish unrelated
native IR; consumers prepend the returned path only while running FIR capture.

Run the focused contract with:

```sh
node --test integration/package-tools/*.test.mjs
```

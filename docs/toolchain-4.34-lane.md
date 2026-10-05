# Lean toolchain and compatibility tooling

Accepted FIR main uses `leanprover/lean4:v4.34.1`. Ordinary feature work
starts from current main and uses that pin. The earlier RC2 migration branch
and its compile smoke are no longer instructions for building current FIR.

## Build and proof commands

```sh
make check
make talos-setup
make talos-check
make tooling-check
```

`make check` covers the FIR build, examples, scalar Wasm surface,
native/LCNF/V8 validation, source trust checks and tooling unit tests.
`make talos-check` separately builds the complete proof cone and forces
direct elaboration of its compiled trust inventories. `make tooling-check`
adds the live Binaryen/profile tests and the compiled Array ownership probe;
it needs the pinned external tools described in
[the tooling CI contract](tooling/CI.md).

The root Makefile selects the shared toolchain-scoped Lake artifact cache.
Mutable `.lake`, `.beam`, `.deps` and temporary inputs stay local to each
worktree. Before direct Lake or Lean Beam commands, use the cache environment
specified in [AGENTS.md](../AGENTS.md).

## Talos overlay

The active proof project is prepared under `.deps/talos-434/project` by
[tooling/talos-434](../tooling/talos-434/README.md). Its tracked inputs are
Lean 4.34.1, Talos `0e05edbcfbb105b33e90c60b4f50e2cf193d9254`,
and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
It mirrors current `integration/talos/FirTalos` proof sources and applies
the reviewed compatibility patches after authenticating their inputs.

The obsolete standalone 4.33 metadata in `integration/talos` has been
removed with W6/root confirmation. That directory supplies maintained proof
sources to the overlay; it is not a separate Lake project.

The trusted-assumption validator authenticates the exact selected compiler
identity and audited source hashes. Compiled W6 trust audits remain separate
from that source identity check. Neither establishes the universal upstream
bridge proposition. The existing `lean433UpstreamBridge` declaration name
is still the registered audited assumption; its spelling does not select
the old toolchain.

## Future toolchain changes

Root owns main pins and migrations. A compatibility experiment uses the
tooling lane or a tooling-owned child worktree, and states its exact compiler
identity. Migration evidence must include the repository gate, the complete
Talos/proof-trust gate, current tooling tests, matched C/Emscripten runtime,
and affected artifact gates. Consumer recipes must be requalified against
the accepted tree rather than kept on an incompatible pin.

Current recipe navigation lives in [build-examples.md](build-examples.md).
The [build/test/performance review](tooling/BUILD_TEST_PERF.md) describes the
command boundaries and remaining tooling gaps.

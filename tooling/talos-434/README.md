# Talos proof cone for Lean 4.34

On the root-owned Lean 4.34 migration candidate, the standard targets use this
tracked Talos overlay:

```sh
make talos-setup
make talos-check
```

The scripts can also be run directly when debugging the migration gate.

`check.sh` repeats the identity-checked setup, then builds
`FirTalos.ConcreteResidentFloat` and the full `FirTalos` umbrella (including
`TrustAudit`). Before building, it runs the fail-closed profile negatives and
the trusted-assumption validator against the overlay project's explicit
toolchain. It authenticates the exact compiler version and commit plus the
W6-reviewed upstream and local checker source hashes. The ordinary no-argument
validator remains the Lean 4.33 audit. All mutable source and Lake state stays under
`.deps/talos-434/` in this worktree. The historical `integration/talos` package
manifest remains available for 4.33 compatibility work; the migration
candidate's standard Talos targets select the authenticated 4.34 overlay.

The immutable inputs are Talos
`0e05edbcfbb105b33e90c60b4f50e2cf193d9254`, mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, and Lean
`4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`). The
tracked manifests and patches have exact SHA-256 checks in `setup.sh`.
`talos.patch` changes only the interpreter's toolchain and mathlib release;
`float-normalization.patch` is retained as the independently reviewed source
repair and is applied only when the copied source does not already contain the
exact `dsimp only at h4 h5 h6 h7` line. The migration branch currently carries
that repair in its tracked source, so setup verifies the newer full Talos source
tree directly and does not duplicate the patch. It fails if a later FIR/W6 edit
changes that reviewed source identity; update the overlay explicitly after a
new proof checkpoint is integrated.

This is audited compatibility evidence, not a kernel proof of the universal
bridge proposition. It is the migration candidate's official Talos gate for
Lean 4.34; it does not change the upstream Talos repository.
The legacy `lean433UpstreamBridge` name is intentionally retained for the one
audited assumption reviewed under both authenticated compiler identities.

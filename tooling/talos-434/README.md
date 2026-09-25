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

`setup.sh` mirrors the current complete `integration/talos/FirTalos` tree into
the isolated project, deleting files removed upstream. It compares the source
inventory and file hashes before and after copying and checks the copied tree
before applying the reviewed Float normalization. Proof-only edits therefore
reach the overlay gate without changing a fixed whole-tree digest. The Float
file remains restricted to its exact reviewed original or normalized hash.
`test-setup.sh` covers changed and deleted proof files, copy corruption,
source mutation during copying, and changed pinned identities.

The immutable inputs are Talos
`0e05edbcfbb105b33e90c60b4f50e2cf193d9254`, mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, and Lean
`4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`). The
tracked manifests and patches have exact SHA-256 checks in `setup.sh`.
`talos.patch` changes only the interpreter's toolchain and mathlib release;
`setup.sh` applies it with `--unidiff-zero` only after authenticating the exact
Talos commit and both source-file hashes, then checks both resulting hashes.
The focused setup test applies the patch to a fixture pinned by the same
before/after hashes. This is necessary because the revision hunk has no
trailing context; the expected identity and output are still fail-closed.
`float-normalization.patch` applies W6's independently reviewed one-line
`dsimp only at h4 h5 h6 h7` when the source is still at the original reviewed
hash. It accepts the exact normalized hash when that line has already landed.
The complete `FirTalos` proof tree is mirrored from the current checkout with
before/after and copied-tree hash checks, so reviewed proof additions and
deletions reach the isolated RC2 gate without changing a fixed whole-tree
digest. The Float source and umbrella entry point remain individually pinned;
other proof-tree edits must be reviewed through the normal W6 handoff.

This is audited compatibility evidence, not a kernel proof of the universal
bridge proposition. It is the migration candidate's official Talos gate for
Lean 4.34; it does not change the upstream Talos repository.
The legacy `lean433UpstreamBridge` name is intentionally retained for the one
audited assumption reviewed under both authenticated compiler identities.

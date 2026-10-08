# Talos proof cone for Lean 4.34.1

The standard proof targets use this tracked setup with a pinned upstream Talos
revision that natively selects Lean and mathlib 4.34.1:

```sh
make talos-setup
make talos-check
make proof-trust
```

The scripts can also be run directly when debugging the proof gate.

`check.sh` repeats the identity-checked setup, then builds
`FirTalos.ConcreteResidentFloat` and the full `FirTalos` umbrella (including
`TrustAudit`), then invokes the shared proof-trust runner to force direct
elaboration of the audit even when Lake reuses the compiled module.
`make proof-trust` uses the same runner independently: it refreshes the overlay,
authenticates the compiler/source profile, builds the audit's dependency cone,
and runs `lake env lean FirTalos/TrustAudit.lean` in the prepared project.
Before building, `check.sh` runs the fail-closed profile negatives and
the trusted-assumption validator against the overlay project's explicit
toolchain. It authenticates the exact compiler version and commit plus the
W6-reviewed upstream and local checker source hashes. The ordinary no-argument
validator uses the accepted Lean 4.34.1 profile. All mutable source and Lake state stays under
`.deps/talos-434/` in this worktree. The former standalone
`integration/talos` package metadata and Lean 4.33 wrapper are retired.
Blueprint and retained-initializer consumers use the same prepared
`.deps/talos-434/project` path.

`setup.sh` mirrors the current complete `integration/talos/FirTalos` tree into
the isolated project, deleting files removed upstream. It compares the source
inventory and file hashes before and after copying and checks the copied tree
before applying the reviewed Float normalization. Proof-only edits therefore
reach the overlay gate without changing a fixed whole-tree digest. The Float
file remains restricted to its exact reviewed original or normalized hash.
`test-setup.sh` covers changed and deleted proof files, copy corruption,
source mutation during copying, and changed pinned identities.

The immutable inputs are Talos
`80644390de3ad4db3055445259a034413ae41577`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean
`4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). The
tracked manifests and remaining Float patch have exact SHA-256 checks in
`setup.sh`. The upstream interpreter toolchain, lakefile and manifest are
authenticated in place; no upstream source or dependency metadata is patched.
Both staged and unstaged tracked upstream changes are rejected. The setup
tests cover wrong revisions, changed sources and compiler pins as well as
source mirroring. The obsolete `talos.patch` and its old-toolchain fixtures
are removed. Upstream's native manifest exactly matches the former overlay's
4.34.1 manifest, so downstream dependency revisions remain unchanged.

An existing scratch checkout at the old Talos revision fails authentication.
Preserve that whole worktree-local `.deps/talos-434` directory under an unused
backup name before rerunning setup; do not reset a dirty checkout or reuse
its mutable Lake state for the new revision. Setup clones the exact revision
into fresh local state. It does not delete old checkouts or installed compilers.

Talos has no published releases or tags at the migration date. This is an exact
upstream commit pin, not an upstream stable-release designation. See
[`docs/talos-4341-consolidation-evaluation.md`](../../docs/talos-4341-consolidation-evaluation.md)
for the source/API changes and migration acceptance boundary.
`float-normalization.patch` applies W6's independently reviewed one-line
`dsimp only at h4 h5 h6 h7` when the source is still at the original reviewed
hash. It accepts the exact normalized hash when that line has already landed.
The complete `FirTalos` proof tree is mirrored from the current checkout with
before/after and copied-tree hash checks, so reviewed proof additions and
deletions reach the isolated stable gate without changing a fixed whole-tree
digest. The Float source and umbrella entry point remain individually pinned;
other proof-tree edits must be reviewed through the normal W6 handoff.

This is audited compatibility evidence, not a kernel proof of the universal
bridge proposition. It is the official Talos gate for
Lean 4.34.1; it does not change the upstream Talos repository.
The legacy `lean433UpstreamBridge` name is intentionally retained for the one
audited assumption reviewed under both authenticated compiler identities.

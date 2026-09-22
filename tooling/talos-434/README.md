# Isolated Talos proof cone for Lean 4.34

From FIR's `tooling/lean-4.34` worktree, run:

```sh
bash tooling/talos-434/setup.sh
bash tooling/talos-434/check.sh
```

`check.sh` repeats the identity-checked setup, then builds
`FirTalos.ConcreteResidentFloat` and the full `FirTalos` umbrella (including
`TrustAudit`). All mutable source and Lake state stays under
`.deps/talos-434/` in this worktree. The normal 4.33
`integration/talos` setup, toolchain, manifest, and package directory are
untouched.

The immutable inputs are Talos
`0e05edbcfbb105b33e90c60b4f50e2cf193d9254`, mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, and Lean
`4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`). The
tracked manifests and patches have exact SHA-256 checks in `setup.sh`.
`talos.patch` changes only the interpreter's toolchain and mathlib release;
`float-normalization.patch` applies W6's independently reviewed one-line
`dsimp only at h4 h5 h6 h7` to the generated source view. The setup checks
the complete FIR Talos Lean-source tree before and after this insertion.
It fails if a later FIR/W6 edit changes that reviewed source identity; update
the overlay explicitly after the new proof checkpoint is integrated.

This is a compatibility proof build, not an official migration of FIR or
Talos to 4.34. The separate trusted-assumption/bridge gate remains for root
and W6 to decide; `make check` is not claimed green by this overlay.

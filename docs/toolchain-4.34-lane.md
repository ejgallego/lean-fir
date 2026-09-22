# Lean 4.34 tooling lane

`tooling/lean-4.34` is FIR's official compatibility branch for projects whose
ordinary Lake build uses `leanprover/lean4:v4.34.0-rc2`.  It is based on a
green `main` checkpoint and changes `lean-toolchain` only in this lane.

## Purpose

Use this worktree for FIR work that must inspect, capture, lower, or test a
user project's actual 4.34 module setup.  It replaces disposable FIR source
views and ad-hoc toolchain pins as the starting point for such work.

`main` remains the 4.33 release/integration branch until tooling demonstrates
and lands a deliberate migration.  A feature result derived on this branch is
not automatically a 4.33 result; handoffs state the exact branch head, 4.34
toolchain revision, and any compatibility evidence.

## Ownership and handoff

The tooling lane owns this branch's toolchain pin, Lake compatibility work,
and its 4.34 CI/tooling surface.  A worker requiring 4.34 starts from this
worktree (or a worktree rebased on its accepted head), retains the target
project's original Lake module setup, and does not substitute a hand-built
setup or a detached FIR source view.

Runtime, ABI, semantic-contract, consumer, and W6-proof changes keep their
normal owners.  Toolchain migration into `main` remains an explicit root
integration decision after the required checks pass.

## Compatibility checkpoint (2026-09-15)

At branch head `348f42f832983949dd1514ed700820cf9c6c05c3`, the pin resolves
to Lean `4.34.0-rc2` commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`
and Lake `5.0.0-src+6a10ac8`. The worktree-local Lake cache resolves to the
separate `leanprover--lean4---v4.34.0-rc2` directory. No mutable `.lake`,
`.beam`, or `.deps` state is shared with a 4.33 worker.

| Check | 4.34 result | Boundary |
| --- | --- | --- |
| `lake build` | Pass, 22 jobs | FIR library compiles; only existing deprecation warnings. |
| Example cone | Pass, 42 jobs | Includes pass examples and Wasm emit examples. |
| Scalar Wasm surface | Pass, 163 functions / 5,706 bytes | Native build and Node execution agree. |
| Validation harness unit checks | Pass | 4 + 126 + 6 + 3 + 3 Python tests, Float/external Node tests. |
| `make check` | Fails in V8 validation | All 721 native/LCNF/V8 values agree, but one 4.33-specific external-trace requirement produces four findings. |
| Trust-source audit | Not reached by `make check`; focused command rejects the 4.34 pin | Upstream `AlphaEqv`, `SimpCase`, and `ElimDead` source SHA-256 values are unchanged from 4.33; the audit still requires the literal 4.33 toolchain. |
| Talos package/driver | Isolated full proof cone passes with one W6-approved proof normalization; official gate still pending | `integration/talos/lean-toolchain` and the pinned Talos interpreter remain 4.33; no `make talos-check` under the official pin is claimed. |
| CI | Focused branch smoke is staged; no hosted run claimed | `.github/workflows/lean-434-compat.yml` checks compilation and scalar execution only. Existing full workflow still targets `main`. |

The observed validation drift is confined to
`Fir/Validation/Corpus.lean`'s `generic-uint8-array-get`: Lean 4.34 emits
and executes `Array.get!Internal` but no longer emits or executes
`instInhabitedUInt8`. The value remains `UInt8 255`, equal in all three
backends. Its four findings are missing static external, missing executed
external, exact-count failure, and exact-trace failure. The expected 4.33
trace must not be silently weakened on this branch; the shared corpus owner
should review a version-indexed expectation or a deliberately separate 4.34
fixture. The 4.33 trust axiom and Talos package/toolchain boundary likewise
need root/proof review before any full 4.34 gate is called green.

The first tooling conclusion is therefore: the basic Lake/library and Wasm
driver path already works under 4.34; the blocker is version-pinned validation
and proof-package contracts, not a package-manager failure. A 4.34 CI trigger
should be added only with an explicit, truthful gate policy after those
contracts are reviewed. The branch smoke workflow is expressly not a replacement
for `make check` or `make talos-check`. Feature workers may consume this compatibility branch
for focused 4.34 work but must report these outstanding repository-wide gates.

## Full-cone probe update (2026-09-22)

At clean tooling head `7cbd297872913816f444b81239c648d753130c34`, an
ignored source view compiled the real pinned Talos interpreter at
`0e05edbcfbb105b33e90c60b4f50e2cf193d9254` with Lean
`4.34.0-rc2` and matching mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. Its only Lean-source
change was W6's reviewed `dsimp only at h4 h5 h6 h7` immediately after
`cases memory` in the byte-memory lemma of `ConcreteResidentFloat.lean`.
The actual `FirTalos.ConcreteResidentFloat` cone passed (3,155 jobs), followed
by the full `FirTalos` umbrella including `TrustAudit` (3,231 jobs). This is
strong 4.34 proof-compatibility evidence, not an official Talos pin update or
an unmodified `make talos-check` result. The worktree-local report and log
hashes are in `.deps/float-434-full-cone-report.md`.

A fresh `make check` on the same tracked head still fails the exact four
`generic-uint8-array-get` external-trace findings: all 721 native, LCNF, and
V8 results agree, but 4.34 observes only `Array.get!Internal`, while the
accepted 4.33 contract requires `instInhabitedUInt8` before it. A focused
`scripts/validate_trusted_assumptions.py` run rejects only the literal 4.33
toolchain pin; SHA-256 of each audited upstream `AlphaEqv`, `SimpCase`, and
`ElimDead` source file is byte-for-byte unchanged in the installed 4.34
toolchain. Neither result authorizes silently broadening the corpus or
renaming/recertifying the `lean433UpstreamBridge` axiom. Both remain explicit
root/proof-owner decisions under the full-gate policy below.

The broader tooling gate exposed a separate allocation-ratchet drift in the
ordinary Array probe: 4.34 preserves every returned value but allocates one
copy on the first shared update, then reuses the new Array. The tooling-owned
check now retains its exact 4.33 copy-count expectation and applies an exact,
fail-closed 4.34 expectation. `make -C tooling check` passes with the pinned
Binaryen tools; both raw and packaged Array probes pass. See
`bugs/FIR-BUG-tooling-array-probe-434-copy-ratchet.md`. A subsequent full
`make check` still has only the four corpus findings above (721/721 values
equal), so this tooling repair does not mask the shared-fixture gate.

## Full-gate migration policy to decide

These are owner decisions, not changes made by the tooling lane:

1. The shared corpus owner should bind an **exact** external inventory and
   executed trace to each accepted Lean toolchain identity. For this fixture,
   keep the 4.33 sequence `[instInhabitedUInt8, Array.get!Internal]` unchanged;
   a reviewed 4.34 entry would require exactly `[Array.get!Internal]`, once,
   while preserving the result, boxing/projection forms, and ownership checks.
   An unknown Lean revision or any third sequence must fail closed. Add both
   version-selection and wrong-trace negative tests before calling the 4.34
   differential gate green.
2. Root and the proof owner should decide whether the existing textual
   `lean433UpstreamBridge` can be certified for 4.34 or needs a separately
   named bridge. Equal upstream source bytes for three audited files are useful
   evidence, not by themselves a theorem that the 4.34 compiled pass and
   imported declarations satisfy the 4.33 proof contract. The trust validator
   may accept 4.34 only after that proof/conformance decision is recorded.
3. Root/W6 should pin a Talos interpreter compatible with the **same** 4.34
   toolchain before a 4.34 `make talos-check` is claimed. The current Talos
   interpreter's 4.33 `lean-toolchain` and setup guard are real package
   boundaries, not merely cosmetic strings; no cross-version `.olean` reuse
   or shared mutable `.lake` is permitted.
4. The focused branch smoke may be green independently. A full 4.34 CI job
   should run unmodified `make check` and `make talos-check` only after the
   preceding contracts are reviewed and their exact gates pass locally. A
   migration of `main` remains a separate root decision with green evidence.

## Versioned corpus checkpoint (2026-09-22)

Under root's narrow shared-corpus lease, the `generic-uint8-array-get`
external inventory, executed inventory, exact counts, and ordered trace now
select one of two reviewed obligations by both `Lean.toolchain` and
`Lean.githash`. The 4.33 obligation is unchanged; 4.34 requires exactly one
`Array.get!Internal`. Compile-time guards reject unknown identities,
cross-version identities, the 4.33 trace under 4.34, and a duplicate 4.34
call. The case's value, box/unbox, projection, and ownership obligations are
unchanged.

Lean Beam reports zero diagnostics for the corpus module. The 4.34 `make
check` differential and coverage phases now pass: 721/721 cases across
native, LCNF, and V8, all 2,163 backend results and 2,172 comparisons equal,
with zero findings. The full command still exits at the **unchanged**
trusted-assumption validator, which accepts only the 4.33 toolchain. Thus the
4.34 differential gate is green, while full migration readiness is not.

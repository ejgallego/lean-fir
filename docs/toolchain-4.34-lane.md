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
| Talos package/driver | Not yet tested on 4.34 | `integration/talos/lean-toolchain` and the pinned Talos interpreter remain 4.33. |
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

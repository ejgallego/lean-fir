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

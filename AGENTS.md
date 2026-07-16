# FIR parallel-development rules

These rules apply to every agent and worktree in this repository.

## Branch and worktree discipline

- `main` is integration-only and must stay green. Feature agents must not edit
  or commit directly on it.
- Proof work uses branch `proof/simpcase` in `.worktrees/proof-simpcase`.
- Wasm work uses branch `wasm/talos-runtime` in `.worktrees/wasm-talos`.
- Before editing, run `git status --short --branch` and confirm that the branch
  and worktree match the assigned track.
- Keep `.lake`, `.beam`, and `.deps` local to each worktree. Do not symlink or
  share mutable build state between agents.

## Ownership

- The proof track owns `Fir/LeanIR/Passes/`, proof-specific examples, and
  proof-specific bug cards.
- The Wasm track owns `Fir/Wasm/`, `integration/talos/`, and Wasm-specific bug
  cards.
- The integration owner controls `Fir/LeanIR/Phase.lean`,
  `Fir/LeanIR/Runtime.lean`, `Fir/LeanIR/Interpreter.lean`,
  `Fir/LeanIR/PassCorrectness.lean`, shared examples, root umbrella modules,
  toolchains, manifests outside `integration/talos`, and root build files.
- Documentation within a track may be updated by that track. Changes to
  `README.md`, `docs/pass-correctness-plan.md`, or this file are coordinated
  through the integration owner.

## Shared semantic contracts

The following are shared contracts: impure values and runtime state,
observations, interpreter steps/evaluation, `ObservationRel`, common example
programs, and the semantic Wasm ABI.

If a track needs to change a shared contract:

1. isolate the contract change in its own commit;
2. describe its effect on both tracks;
3. land it on `main` through the integration owner;
4. rebase both feature branches before dependent work continues.

Do not duplicate or locally weaken a shared semantic definition to avoid this
coordination step.

## Integration cadence

- Commit small, coherent, tested vertical slices.
- Rebase on local `main` after every shared-contract change and before every
  handoff. Do not merge `main` into a feature branch.
- Integrate a useful green slice promptly; do not wait for an entire research
  milestone.
- Only the integration owner merges to `main`, using `git merge --ff-only`
  after the feature branch has rebased and passed its checks.
- After one feature branch lands, the other branch rebases on the new `main`
  before its next integration.
- Do not force-push or rewrite another agent's branch.

## Required checks

- Every slice: `git diff --check` and `make check`.
- Wasm/Talos slices: also `make talos-check` after `make talos-setup` has been
  run in that worktree.
- Lean source edits use the repository's Lean Beam workflow during iteration;
  `lake build` remains the final dependency-cone check.
- A failing proof, invariant, or differential test that may expose a semantic
  discrepancy gets a card under `bugs/` before a workaround is added.

## Handoff format

Every handoff to the integration owner reports:

- base commit and head commit;
- completed vertical slice;
- files and shared contracts changed;
- exact checks run and their results;
- bug-card IDs, or `none`;
- known follow-ups.

The worktree must be clean at handoff.

# FIR parallel-development rules

These rules apply to every agent and worktree in this repository.

## Branch and worktree discipline

- `main` is integration-only and must stay green. Feature agents must not edit
  or commit directly on it.
- Lean pass-proof work uses branch `proof/simpcase` in
  `.worktrees/proof-simpcase`.
- W6 concrete-runtime and Wasm-proof work uses branch `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- W7 resident-runtime generation work uses branch `wasm/generation` in
  `.worktrees/wasm-generation`.
- Before editing, run `git status --short --branch` and confirm that the branch
  and worktree match the assigned track.
- Keep `.lake`, `.beam`, and `.deps` local to each worktree. Do not symlink or
  share mutable build state between agents.
- Share only Lake's content-addressed artifact cache across FIR worktrees. For
  direct `lake` or `lean-beam` commands, first run:
  `export LAKE_CACHE_DIR="$(bash "$(git rev-parse --show-toplevel)/scripts/fir-lake-cache-path.sh")" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true`.
  The root `Makefile` initializes and exports the same FIR-local,
  toolchain-scoped location automatically. Its boundary is mode 700. The
  cache is ignored; never commit it or use it in place of a worktree's
  `.lake` state.
- Never use the system `/tmp` directory for FIR source views, build inputs,
  compiler state, package publication, test fixtures, or scratch data. It is
  periodically cleaned. Use an ignored, worktree-local `.deps` path instead;
  when a tool requires a temporary directory, set `TMPDIR` to that persistent
  worktree-local location explicitly.

## Ownership

- The proof track owns `Fir/LeanIR/Passes/`, proof-specific examples, and
  proof-specific bug cards.
- The W6 track owns the concrete layout/runtime and its proofs:
  `Fir/Wasm/Concrete/`, `Fir/Wasm/Concrete.lean`, proof-side lowering and
  handles, `integration/talos/FirTalos/`, W6 roadmap/coverage documents, and
  W6-specific bug cards.
- The W7 track owns resident-runtime generation and consumption:
  `Fir/Wasm/Emit/`, `Fir/Wasm/PrettyFormat.lean`,
  `integration/talos/artifact/`, and W7-specific bug cards. W7 supplies
  executable helpers and acceptance artifacts; it does not claim their W6
  refinement theorems.
- The integration owner controls `Fir/LeanIR/Phase.lean`,
  `Fir/LeanIR/Runtime.lean`, `Fir/LeanIR/Interpreter.lean`,
  `Fir/LeanIR/PassCorrectness.lean`, shared examples, root umbrella modules,
  toolchains, manifests outside `integration/talos`, root build files, the
  symbolic Wasm instruction/module surface, and cross-lane coordination files.
- Documentation within a track may be updated by that track. Changes to
  `README.md`, `docs/pass-correctness-plan.md`, or this file are coordinated
  through the integration owner.
- `coordination/BOARD.md` is the portable coordination snapshot. Only the
  integration owner edits it; lane owners send board updates in the format
  documented there so the board does not become a shared-file race.
- `coordination/lanes/` contains single-writer lane mailboxes. Each lane owner
  edits only its assigned file; the integration owner may seed a mailbox when
  a milestone starts but does not edit another lane's subsequent updates.
  `coordination/lanes/README.md` defines the schema and branch-head resolution
  rule. These mailboxes are the sole exception to integration ownership of
  cross-lane coordination files.

## Milestone-scoped integration lease

- `coordination/BOARD.md` names one integration owner and integration branch
  for each active cross-lane milestone. The lease ends when that milestone is
  linked/accepted, explicitly parked, or explicitly reassigned on the board.
- The integration owner may also own a feature lane when that lane is waiting
  at the shared-contract boundary. The lease does not grant permission to edit
  files owned by another lane.
- Lane owners publish status by committing their own mailbox file on their own
  branch. The integration owner resolves the actual handoff head from the
  named branch, so a mailbox never attempts to contain the hash of the commit
  that contains itself.
- The integration owner synthesizes accepted mailbox updates into
  `coordination/BOARD.md`, validates candidate stacks, and alone fast-forwards
  `main`. No coordination daemon or generated state is required.

## Local agent mailbox

- New operational coordination uses the ignored canonical mailbox at
  `.agents/mailbox/` in the primary FIR checkout. Linked worktrees do not
  create separate mailboxes.
- Follow `docs/MAILBOX_PROTOCOL.md`. A cross-project thread lives in the
  mailbox of the project that owns the requested code change.
- Read `make mailbox-list` and `git worktree list` before claiming a lane. A
  valid acknowledgement records the owner, project-relative worktree, branch,
  base commit, write scope, and publication boundary.
- The local event log complements rather than replaces the tracked
  `coordination/lanes/` handoff and `coordination/BOARD.md` snapshot. Mailbox
  completion does not authorize integration, pushing, publication, worktree
  removal, or branch deletion.

## Shared semantic contracts

The following are shared contracts: impure values and runtime state,
observations, interpreter steps/evaluation, `ObservationRel`, common example
programs, the semantic Wasm ABI, the symbolic Wasm instruction/module surface,
the W6 concrete layout/runtime surface consumed by W7, and resident-helper
signatures consumed by W6 proofs.

If a track needs to change a shared contract:

1. isolate the contract change in its own commit;
2. add a contract-queue record to the coordination board;
3. describe its effect on every consumer;
4. land it on `main` through the integration owner;
5. rebase the affected feature branches before dependent work continues.

Do not duplicate or locally weaken a shared semantic definition to avoid this
coordination step.

## W6/W7 pipeline

W6 and W7 are expected to proceed concurrently. W7 may implement and test
resident helper `N + 1` while W6 proves that stable helper `N` implements its
concrete-runtime contract.

- W7 marks a helper `generation-ready` only after its standalone and linked
  external-engine checks pass. The handoff records the helper signature,
  contract-base commit, and artifact digest.
- W6 marks it `contract-proved` only after the implementation-to-concrete-host
  theorem and its dependency-cone checks pass.
- Integration marks it `linked/accepted` when the linked artifact and relevant
  import-closure checks land.

A helper being generation-ready is deliberately distinct from its refinement
theorem. Contract or signature changes return the helper to the contract queue;
they do not silently invalidate proof work.

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
- W7 artifact slices also run `bash integration/talos/artifact/check.sh`.
  Browser checks run through that script when `FIR_BROWSER` is set.
- Lean source edits use the repository's Lean Beam workflow during iteration;
  `lake build` remains the final dependency-cone check.
- A failing proof, invariant, or differential test that may expose a semantic
  discrepancy gets a card under `bugs/` before a workaround is added.

## Handoff format

Every handoff to the integration owner reports:

- base commit and head commit;
- completed vertical slice;
- files and shared contracts changed;
- lane name and contract-base commit;
- exact checks run and their results;
- bug-card IDs, or `none`;
- known follow-ups.

The worktree must be clean at handoff.

For a parallel milestone, commit the same information in the lane's assigned
`coordination/lanes/*.md` mailbox. `functional-head` identifies the last code
or proof commit; the integration owner obtains the containing status commit
from the branch named in the mailbox. A `ready` mailbox with
`clean-at-update: false` is invalid.

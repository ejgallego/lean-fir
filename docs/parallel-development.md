# Parallel proof, Wasm proof, and Wasm generation

FIR develops compiler-pass proofs, the W6 concrete-runtime proof, and W7
resident-runtime generation concurrently from one shared final-impure semantic
boundary. The root `AGENTS.md` contains the normative rules; this document
explains the workflow for maintainers.

## Worktree layout

The repository root remains the `main` integration worktree:

```text
fir/                              main
fir/.worktrees/proof-simpcase/    proof/simpcase
fir/.worktrees/wasm-talos/        wasm/talos-runtime
fir/.worktrees/wasm-generation/   wasm/generation
fir/.worktrees/native-validation/ validation/interpreter-corpus
```

Each worktree has independent source, index, `.lake`, `.beam`, and `.deps`
state. They share Git objects and branch references only.

The initial provisioning commands are:

```sh
git worktree add .worktrees/proof-simpcase -b proof/simpcase main
git worktree add .worktrees/wasm-talos -b wasm/talos-runtime main
git worktree add .worktrees/wasm-generation -b wasm/generation main
git worktree add .worktrees/native-validation \
  -b validation/interpreter-corpus main
```

The W6 worktree owns concrete-runtime definitions and proofs. The W7 worktree
owns resident helper generation, artifact linking, clients, and packaging.
They must not share an index or mutable build state even when their current
file sets do not overlap.

At startup, an agent runs `git status --short --branch` and checks its lane
against `AGENTS.md`. This deliberately remains a small human-auditable
protocol. Add harness automation only for a repeated, mechanically detectable
failure that the branch/worktree split does not already prevent.

Agents read and write new operational messages only through the primary
checkout's ignored `.agents/mailbox/`, using `docs/MAILBOX_PROTOCOL.md` and
`make mailbox-check`. This avoids per-worktree message forks. The tracked
`coordination/lanes/*.md` records remain the portable, committed handoff state;
the local mailbox does not replace them.

## Integration loop

An agent finishes a small vertical slice, commits it, then rebases its clean
worktree on the current local `main`:

```sh
git rebase main
make check
```

Both Wasm tracks additionally run:

```sh
make talos-check
```

W7 artifact slices also run:

```sh
bash integration/talos/artifact/check.sh
```

After reviewing the handoff, the integration owner advances `main`:

```sh
git merge --ff-only <feature-branch>
```

Branches affected by the slice then rebase on the advanced `main`. This
produces frequent integration without merge commits or agents racing to modify
an integration worktree.

## Track boundaries

The Lean proof track starts with the local `simpCase` transformation kernel,
preservation theorems, and conformance of captured Lean 4.33 checkpoints.

W6 owns Talos/concrete runtime definitions, representation relations, compiler
simulation, structured-fault proofs, and the theorem relating a stable
resident helper to its concrete host contract. W7 owns the executable resident
helper, checked linking, external-engine execution, import-closure inspection,
and consumer package.

The tracks consume the same impure runtime, interpreter observations, Wasm
ABI, symbolic instruction/module surface, and selected concrete layouts.
Those boundaries are coordinated because an unannounced change can invalidate
another lane. A necessary contract change is landed separately and affected
worktrees rebase before dependent work continues. A Git commit plus an
artifact digest identifies the consumed contract; this workflow does not
require a prematurely frozen numeric ABI version.

## W6/W7 pipeline

W6 and W7 are intentionally concurrent rather than alternate leases on one
worktree:

```text
W7: implement and execute helper N ── handoff ──> W6: prove helper N
W7: implement helper N+1          ─────────────> runs at the same time
```

The synchronization states are `generation-ready`, `contract-proved`, and
`linked/accepted`. A handoff includes the helper signature, source commit,
concrete-contract base, artifact digest, exact checks, and known proof
preconditions. A concrete-layout, runtime-contract, symbolic-surface, or helper
signature change is a contract barrier and goes through `main`.

`coordination/BOARD.md` is the portable snapshot of lane activity and contract
barriers. Only the integration owner edits it. Other owners send a compact
update rather than modifying the board from multiple branches.

## Integration criteria

A slice is ready when it is narrowly scoped, its worktree is clean, all
required checks pass, semantic assumptions are explicit, and possible
discrepancies have bug cards. A research milestone may span many such slices;
keeping `main` green takes precedence over landing incomplete work early.

Use the handoff format in `AGENTS.md` so the integration owner can determine
whether a fast-forward is safe without reconstructing the agent's context.

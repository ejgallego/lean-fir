# Parallel proof and Wasm development

FIR develops compiler-pass proofs and the Wasm backend concurrently from one
shared final-impure semantic boundary. The root `AGENTS.md` contains the
normative rules; this document explains the workflow for maintainers.

## Worktree layout

The repository root remains the `main` integration worktree:

```text
fir/                              main
fir/.worktrees/proof-simpcase/    proof/simpcase
fir/.worktrees/wasm-talos/        wasm/talos-runtime
```

Each worktree has independent source, index, `.lake`, `.beam`, and `.deps`
state. They share Git objects and branch references only.

The initial provisioning commands are:

```sh
git worktree add .worktrees/proof-simpcase -b proof/simpcase main
git worktree add .worktrees/wasm-talos -b wasm/talos-runtime main
```

## Integration loop

An agent finishes a small vertical slice, commits it, then rebases its clean
worktree on the current local `main`:

```sh
git rebase main
make check
```

The Wasm track additionally runs:

```sh
make talos-check
```

After reviewing the handoff, the integration owner advances `main`:

```sh
git merge --ff-only <feature-branch>
```

The other feature branch then rebases on the advanced `main`. This produces
frequent integration without merge commits or two agents racing to modify the
integration worktree.

## Track boundaries

The proof track starts with the local `simpCase` transformation kernel,
preservation theorems, and conformance of captured Lean 4.32 checkpoints. The
Wasm track starts with Talos implementations for constructor allocation, tag
lookup, and object projection.

Both tracks consume the same impure runtime, interpreter observations, and
Wasm ABI. Those definitions are integration-owned because an uncoordinated
change would invalidate work in both branches. A necessary contract change is
landed separately and rebased into both worktrees before either track builds
on it.

## Integration criteria

A slice is ready when it is narrowly scoped, its worktree is clean, all
required checks pass, semantic assumptions are explicit, and possible
discrepancies have bug cards. A research milestone may span many such slices;
keeping `main` green takes precedence over landing incomplete work early.

Use the handoff format in `AGENTS.md` so the integration owner can determine
whether a fast-forward is safe without reconstructing the agent's context.

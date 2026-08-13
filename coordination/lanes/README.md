# FIR lane mailboxes

These files are small, human-maintained handoff records. They replace routine
copy/paste between sessions; they do not replace Git branches, clean
worktrees, tests, or the integration owner's board.

They are tracked milestone snapshots, not the local operational mailbox. New
requests and acknowledgements use the primary checkout's ignored
`.agents/mailbox/` and `docs/MAILBOX_PROTOCOL.md`; a ready lane still commits
the schema below here before integration.

## Single-writer ownership

| File | Owner | Branch |
|---|---|---|
| `wasm-gen.md` | wasm-gen | `wasm/generation` |
| `wasm-proof.md` | wasm-proof | `wasm/talos-runtime` |
| `lcnf-proof.md` | lcnf-proof | `proof/simpcase` |
| `test-fixtures.md` | test-fixtures | `validation/closure-ownership-fixtures` |

The integration owner may create the initial records for a milestone. After
that bootstrap, each owner edits only its own file. Mailbox updates are normal
commits on the lane branch; agents never edit `coordination/BOARD.md`.

## Record schema

```text
lane:
owner:
branch:
worktree:
state: active | waiting | ready | blocked | released | parked
base:
functional-head:
contract-base:
clean-at-update: true | false
slice:
files:
contracts: none | <contract IDs and effects>
checks: not-run | <exact commands and results>
bug-cards: none | <IDs>
blockers: none | <dependencies>
handoff: none | <what integration may land>
next:
```

`functional-head` is the last code, proof, fixture, or artifact commit. It is
not the mailbox commit itself. Integration resolves the containing handoff
head with `git rev-parse <branch>` and verifies that the worktree is clean.
This avoids an impossible self-referential commit hash.

Use `waiting` when another lane must act first. Use `blocked` only for an
actual impasse, not an ordinary dependency. Use `ready` only after all checks
required by `AGENTS.md` pass and the worktree is clean.

## Integration consumption

The integration owner reads a mailbox directly from its branch, for example:

```sh
git show wasm/talos-runtime:coordination/lanes/wasm-proof.md
```

The owner validates the reported head and checks, updates the portable board,
and lands only the green dependency-ordered slice. There is intentionally no
script, lock service, or generated coordination database.

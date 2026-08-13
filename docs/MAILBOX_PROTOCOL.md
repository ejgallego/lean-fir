# Agent Mailbox Protocol

The agent mailbox is a small local event log for coordinating work without
turning branch or worktree state into a task database. It supports two common
cases:

1. agents working in different linked worktrees of the same project; and
2. agents coordinating changes between dependent projects.

Mailbox contents are local coordination state. They are ignored by Git and do
not replace commits, tracked design documents, issues, or pull requests as the
durable record of a decision.

## Canonical Mailbox

Each project has one canonical mailbox:

```text
<primary-checkout>/.agents/mailbox/
```

The primary checkout is the stable root checkout shown first by
`git worktree list --porcelain`. Agents in linked worktrees must use that
mailbox rather than creating `.agents/` below their current worktree. The
repository commands resolve the primary checkout automatically:

```bash
make mailbox-check
make mailbox-list
```

Use `--mailbox PATH` only for an explicit alternate or test mailbox.

## Thread Home And Addressing

A thread lives in the canonical mailbox of the project that owns the requested
code change.

- A FIR agent requesting work from another FIR agent uses the FIR mailbox.
- An Illuminate agent requesting a FIR generator change uses the FIR mailbox.
- A FIR agent requesting Illuminate validation uses the Illuminate mailbox.

All request, acknowledgement, update, completion, and closure messages remain
in the same thread home. Participants use `project/agent` addresses such as:

```text
fir/root
fir/wasm-gen
lean-zip/root
illuminate/hit-scene
```

Use `project/*` when any agent in the destination project may claim the work;
a concrete `project/agent` recipient may be claimed only by that agent. For
work spanning more than one owning project, open one thread per project and
link them with `parent-thread` or `depends-on`; do not grant ambiguous write
ownership across repositories in one thread.

## Message Files

Protocol v1 stores one immutable Markdown file per message directly in the
mailbox directory:

```text
.agents/mailbox/ROOT-FIR-20260813-001.md
.agents/mailbox/FIR-ROOT-20260813-001.md
```

The filename must equal `<message-id>.md`. IDs have the form:

```text
<FROM>-<TO>-<YYYYMMDD>-<NNN>
```

`FROM` and `TO` are short uppercase project or agent codes. The date is the
local date from the message timestamp, and `NNN` is a sender-controlled daily
sequence. A reply receives a new message ID and retains the original request's
`thread-id`.

Never edit a delivered message. Corrections and changed decisions are new
`update`, `handoff`, `completion`, or `cancellation` messages. Each new message
must reply to the current tail of its thread, producing a linear event chain.
This makes ownership and the latest state unambiguous.

A file is delivered only after `make mailbox-check` accepts it. Correct or
remove a newly written malformed file before anyone replies; immutability
applies once the file validates. A reply cannot repair an invalid graph node.

## Header

Every message starts with a deliberately restricted front matter header. Each
field is one line; protocol v1 does not use nested YAML values.

```markdown
---
protocol: agent-mailbox/v1
message-id: ROOT-FIR-20260813-001
thread-id: ROOT-FIR-20260813-001
in-reply-to:
time: 2026-08-13T14:30:00+02:00
from: lean-zip/root
to: fir/*
kind: request
state: open
requires-ack: true
subject: persist interpreted constants across calls
---

## Request

Describe the problem and evidence.

## Acceptance

- State the observable completion conditions.

## Constraints

- State retained ownership, prohibited approaches, and publication limits.
```

Required fields for every message are:

- `protocol`: exactly `agent-mailbox/v1`;
- `message-id`: the immutable message identity;
- `thread-id`: the opening request's message ID;
- `in-reply-to`: empty for the request, otherwise the current thread tail;
- `time`: ISO 8601 with `Z` or an explicit UTC offset;
- `from` and `to`: `project/agent` addresses;
- `kind` and `state`: one of the combinations below; and
- `subject`: a concise behavior-oriented summary.

A request also requires `requires-ack: true` or `false`. Normal implementation
and investigation requests use `true`. `false` is reserved for a no-claim
request that the requested project may complete directly; it does not open an
unowned stream of work updates. An acknowledgement and a handoff require an
`owner` address. `from` and `owner` must name concrete agents; only `to` may use
the `project/*` wildcard. Completion, closure, and cancellation messages
require `disposition`, ensuring that terminal coordination state names its
durable outcome.

The following operational fields are optional:

- `owner`: current `project/agent` owner;
- `worktree`: project-relative `.worktrees/<slug>` or `none`;
- `branch`: the implementation branch;
- `base` and `head`: abbreviated or full 7--64 character hexadecimal Git
  object IDs;
- `worktree-state`: `clean` or `dirty` (omit it when `worktree` is `none`);
- `publication`: `local-only`, `pushed`, `draft-pr`, or `published`;
- `disposition`: one of the durable outcomes defined below;
- `parent-thread`: a parent coordination thread; and
- `depends-on`: a comma-separated list of prerequisite thread IDs.

`owner` appears only on acknowledgement and handoff messages; `disposition`
appears only on completion, closure, and cancellation messages; and
`parent-thread` and `depends-on` appear only on opening requests. Linked thread
IDs are syntax-checked locally, but may name threads in another project's
mailbox and therefore are not required to exist in the current mailbox.
Optional fields must be omitted rather than left empty. Dependency lists cannot
contain the current thread or repeat an ID.

Publication states describe observable exposure: `local-only` has no remote
branch, `pushed` has a remote branch but no PR, `draft-pr` has a draft PR, and
`published` has a non-draft PR or an equivalent public review surface.

Disposition values describe a completion or termination outcome:

| Disposition | Meaning |
| --- | --- |
| `ready-for-review` | Work or evidence is complete and awaits requester review. |
| `implemented` | The requested behavior has a durable implementation. |
| `decided` | An investigation or interface decision has a durable conclusion. |
| `rejected` | The request was considered and intentionally declined. |
| `no-action` | Investigation found that no change is needed. |
| `landed` | The result was merged or otherwise adopted. |
| `superseded` | Another recorded thread or result replaced this one. |
| `archived` | Useful evidence was retained outside the active mailbox. |
| `discarded` | No result or evidence needs to be retained. |

## Kinds And States

Protocol v1 uses a small state machine:

```text
open --acknowledgement--> claimed
claimed --update/handoff--> claimed | in-progress | blocked
in-progress | blocked --update/handoff--> in-progress | blocked
claimed | in-progress | blocked --completion--> completed --closure--> closed
open --direct completion when requires-ack is false--> completed
open | claimed | in-progress | blocked --cancellation--> cancelled
```

The message kinds are:

| Kind | State | Meaning |
| --- | --- | --- |
| `request` | `open` | Open a new thread. |
| `acknowledgement` | `claimed` | Claim ownership and name the lane. |
| `update` | `claimed`, `in-progress`, or `blocked` | Add evidence, a decision, or a blocker. |
| `handoff` | `claimed`, `in-progress`, or `blocked` | Transfer ownership or a dependency. |
| `completion` | `completed` | Finish implementation or investigation. |
| `closure` | `closed` | The requester accepts the completion. |
| `cancellation` | `cancelled` | Terminate without completion. |

Do not invent ad hoc kinds for ordinary correspondence. Record a decision as
an `update` when the thread remains active, or as a `completion` when the
request asked only for an investigation or decision. The requester accepts a
completed decision with `closure`.

If `requires-ack` is `true`, no work-state transition may precede an
acknowledgement. The acknowledgement sender and owner must be the same agent in
the requested project. Updates may come from the current owner or the
requesting project; handoff and completion come from the current owner. A
handoff keeps ownership in the requested project. Cancellation comes from the
requesting project or current owner, and closure comes from the project that
opened the request. Replies address the other participating project, or the
shared project for same-project threads. Closed and cancelled threads are
terminal.

## Worktree Ownership

Before opening or claiming an implementation lane, read the mailbox and run:

```bash
git worktree list
```

The primary checkout remains the stable coordination base. New implementation
work normally uses:

```bash
git worktree add -b <type>/<slug> .worktrees/<slug> <base-commit>
```

An implementation acknowledgement should record the project-relative
worktree, branch, base commit, intended write scope, and publication boundary.
Write scope stays
in the Markdown body so paths can be listed clearly:

```markdown
---
protocol: agent-mailbox/v1
message-id: FIR-ROOT-20260813-001
thread-id: ROOT-FIR-20260813-001
in-reply-to: ROOT-FIR-20260813-001
time: 2026-08-13T15:10:00+02:00
from: fir/wasm-gen
to: lean-zip/root
kind: acknowledgement
state: claimed
owner: fir/wasm-gen
worktree: .worktrees/wasm-generation
branch: wasm/generation
base: 515bf40
publication: local-only
subject: persistent package interpreter accepted
---

## Write Scope

- `Fir/Wasm/Emit/`
- `integration/talos/artifact/`

No push or public PR is authorized.
```

The claim prevents another agent from opening an overlapping lane. A later
handoff should name the new owner and the checkpoint it may consume.

## Completion Checkpoints

A completion reports the observable result and enough exact identity for a
dependent agent to consume it:

```markdown
---
protocol: agent-mailbox/v1
message-id: FIR-ROOT-20260813-002
thread-id: ROOT-FIR-20260813-001
in-reply-to: FIR-ROOT-20260813-001
time: 2026-08-13T18:20:00+02:00
from: fir/wasm-gen
to: lean-zip/root
kind: completion
state: completed
worktree: .worktrees/wasm-generation
branch: wasm/generation
base: 515bf40
head: abc1234
worktree-state: clean
publication: local-only
disposition: ready-for-review
subject: persistent package interpreter validated
---

## Outcome

Summarize behavior and compatibility.

## Validation

Record only the review-relevant checks and artifact identities.

## Remaining Work

State explicit follow-up or `None`.
```

Completion does not authorize pushing, opening a PR, deleting a worktree, or
deleting a branch. Those remain explicit maintainer actions. Public PR bodies
must not include local mailbox paths, worktree names, command transcripts, or
routine coordination notes.

## Durability And Cleanup

Before closure, the completion or closure message identifies the durable home
of the outcome:

- a commit or landed pull request;
- a retained branch for useful or rejected experimental evidence;
- a tracked design document; or
- an explicit decision that the evidence is disposable.

Delete mailbox files only when the thread is `closed` or `cancelled` and its
durable disposition is recorded. Delete the complete thread, not selected
events. Open, claimed, blocked, completed-but-unclosed, and unacknowledged
threads remain.

Mailbox deletion does not authorize worktree or branch deletion. Worktree
retirement separately confirms cleanliness, commit reachability, remote/PR
state, and maintainer approval.

## Commands

Validate all v1 messages and thread transitions:

```bash
make mailbox-check
```

Run the focused protocol contract tests with `make mailbox-test`.

List active threads:

```bash
make mailbox-list
```

The human-readable list includes the latest recorded lane checkpoint
(worktree, branch, base/head, cleanliness, and publication) when present.
JSON output contains the protocol marker, resolved mailbox path, ignored
filenames, and the same thread summaries. A summary is an index into the
immutable event files, not a replacement for their message bodies.

Include terminal threads or emit JSON:

```bash
node scripts/mailbox.mjs list --all
node scripts/mailbox.mjs list --json
```

Both commands work from the primary checkout or any linked worktree. For an
explicit mailbox:

```bash
node scripts/mailbox.mjs check --mailbox /path/to/.agents/mailbox
```

Every Markdown file other than `README.md` is treated as a v1 message, so an
obsolete directional ledger fails validation instead of silently remaining in
the mailbox. Non-Markdown files, `README.md`, and subdirectories are ignored
and reported so stale mailbox contents remain visible.

## FIR Durable Coordination Boundary

FIR deliberately has two coordination layers:

- `.agents/mailbox/` is ignored local operational state. New requests,
  acknowledgements, decisions, blockers, handoffs, completions, and closures
  use the immutable protocol in this document.
- `coordination/lanes/*.md` and `coordination/BOARD.md` are tracked portable
  milestone snapshots. Lane owners continue committing their single-writer
  status file, and the integration owner continues synthesizing the board.

A v1 completion does not replace the standard FIR handoff fields or authorize
integration. When a slice becomes ready, its owner records the durable status
in the assigned tracked lane file; integration verifies that commit and its
checks as before.

Directional files such as `root-to-wasm-gen.md` created before this protocol
are legacy ledgers. Preserve active evidence under an ignored `legacy/`
subdirectory, but do not append new requests to them. Linked worktrees must
stop creating independent mailboxes: every new v1 thread uses the primary FIR
checkout's canonical `.agents/mailbox/`.

# FIR parallel-development rules

These rules apply to every agent and worktree in this repository.

## Autonomy and coordination

- Work autonomously within the agreed milestone and lane: implementation, proof
  iteration, tests, local commits, and selection of the next lemma do not need
  root permission. Explicit user stops and narrower file leases still apply.
- Coordinate when another owner must act: shared contracts, overlapping edits,
  dependencies/blockers, material scope decisions, or useful integration results.
  Do not turn local proof steps into permission requests.
- Use one thread per independently consumable result, not per lemma. Update it
  when a decision, dependency, ownership, or checkpoint changes. Do not acknowledge
  acknowledgements, repeat unchanged blockers, or open closure-confirmation threads.
- Read relevant mailbox state at task entry, handoff, or a dependency decision;
  do not poll between proof steps. Unrelated arrivals do not preempt the active
  milestone unless the maintainer or a shared-contract change requires it.
- Judge proof progress by premises discharged and executable consequences, not
  lemma counts. If blocked, advance an independent obligation of the same theorem
  or report the blocker; do not manufacture wrappers or status chores.

## Worktrees and build state

`main` is integration-only. Before editing, run `git status --short --branch`
and confirm the assigned branch/worktree. Before claiming a lane, also read
`scripts/mailbox list --for <lane-address>` and `git worktree list`.

| Track | Branch | Worktree under `.worktrees/` |
| --- | --- | --- |
| Pass proofs | `proof/simpcase` | `proof-simpcase` |
| W6 concrete runtime/proofs | `wasm/talos-runtime` | `wasm-talos` |
| W7 generation | `wasm/generation` | `wasm-generation` |
| Compatibility/tooling | `tooling/lean-4.34` | `tooling-lean-4.34` |
| Lean-zip performance | `perf/lean-zip-loop` | `lean-zip-perf` |

Toolchain migrations and main pins are root-owned. Compatibility experiments
use the official tooling lane or a track-owned child, not ad-hoc source views
or local pin overrides. After migration, ordinary feature work uses accepted
main's toolchain; no detour through an obsolete compatibility branch is needed.

Keep mutable `.lake`, `.beam`, and `.deps` local to each worktree, without
symlinks/shared state. Share only the ignored, mode-700, toolchain-scoped Lake
content-addressed cache. Before direct Lake or Lean Beam commands run:

```sh
export LAKE_CACHE_DIR="$(bash "$(git rev-parse --show-toplevel)/scripts/fir-lake-cache-path.sh")" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
```

The root Makefile exports this automatically. Never substitute the cache for
local `.lake` state. Never use system `/tmp` for FIR inputs, scratch, fixtures,
source views, compiler state or publications; use ignored worktree-local
`.deps` and set `TMPDIR` there when needed.

## Ownership

| Owner | Write scope |
| --- | --- |
| Pass-proof lane | `Fir/LeanIR/Passes/`, proof examples and bug cards |
| W6 | `Fir/Wasm/Concrete/`, `Fir/Wasm/Concrete.lean`, proof-side lowering/handles, `integration/talos/FirTalos/`, W6 plans/coverage and bug cards |
| W7 | `Fir/Wasm/Emit/`, `Fir/Wasm/PrettyFormat.lean`, `integration/talos/artifact/`, W7 bug cards |
| Lean-zip performance | `integration/lean-zip/` benchmarks, package ratchets and performance evidence; not manifests or general generation |
| Root | Shared semantics/ABI/instruction surface, `Fir/LeanIR/{Phase,Runtime,Interpreter,PassCorrectness}.lean`, shared examples, root umbrellas/build files, main pins/migrations, manifests outside `integration/talos`, cross-lane coordination |

Track owners may update their own documentation. Coordinate changes to
`README.md`, `docs/pass-correctness-plan.md`, `AGENTS.md`, or another owner's
files through root. Only root edits `coordination/BOARD.md`; each lane alone
edits its `coordination/lanes/*.md` snapshot after initial root seeding.
See `coordination/lanes/README.md` for the schema.

`fir/root` is the standing integration owner (maintainer assignment,
2026-09-09, until reassigned). It serializes integration and resolves shared
dependencies; lane owners choose local implementation steps. W6/W7 do not
inherit root ownership when it is idle. A milestone ends its file lease, not
the standing role. Root may also own a feature lane, but cannot implicitly edit
another lane's files. The board records cross-lane milestone ownership/leases.

## Shared semantic contracts

Shared contracts include impure values/runtime, observations and
`ObservationRel`, interpreter execution, common examples, semantic Wasm ABI,
symbolic instructions/modules, W6 layout/runtime consumed by W7, and resident
helper signatures consumed by W6.

Isolate a shared change in its own commit, describe affected consumers, ask
root to record the contract queue, and land through root. Affected lanes rebase
before dependent work. Never duplicate or weaken a definition to evade this.

W6/W7 proceed concurrently: W7's `generation-ready` means standalone/linked
engine checks passed with signature, contract base and artifact digest; W6's
`contract-proved` means implementation-to-host refinement and its proof cone
passed; integration's `linked/accepted` means linked/import-closure checks
landed. These claims are distinct. Signature/contract changes return to the queue.

Lean-zip performance runs one measured experiment from an immutable accepted
package. It needs a narrow W7 lease before editing W7 implementation. Use
focused differentials and balanced benchmarks; discard losers or hand repeatable
winners to W7 for complete gates. Experiments do not open W6 proof requests;
only generation-accepted winners do. Root integrates.

## Mailbox and checkpoints

Use the primary checkout's ignored `.fir-mailbox/`, never a worktree copy.
`docs/MAILBOX_PROTOCOL.md` defines event syntax and transitions; consult it
when sending or deciding a handoff, not before every edit.

- Draft under local `.deps/`, then `scripts/mailbox deliver <draft>`; never
  write canonical events directly. Delivery normally sends the `codex queue`
  doorbell. In a restricted Codex shell, use `--no-notify` and run `codex queue`
  as a separate direct command: the child process may not inherit access to the
  Codex state database. If direct queueing also fails, leave the event intact
  and request state access; never edit the database by hand. The
  `scripts/mailbox route` command maps stable roles to current sessions;
  session UUIDs are local state.
  Notification failure does not undo delivery.
- A claim records owner, worktree, branch, base, write scope and publication
  boundary. Cross-project requests live with the project owning the code.
- A clean exact `integrationCheckpoint` pins what root reviews/lands. Preserve
  that object; unless explicitly paused, continue in-scope on the same lane
  branch or a successor. Root never substitutes the latest branch tip.
  Without an exact checkpoint, the legacy branch-tip handoff stays frozen.
- Update tracked lane snapshots at meaningful milestone/scope changes,
  preferably in a functional commit. No separate status-only commit is required
  per lemma, acknowledgement, rebase or handoff. Historical snapshots are not
  live backlogs; use Git ancestry and current mailbox decisions.
- Mailbox completion does not itself authorize landing, pushing, PRs, deletion
  or cleanup. Root owns green main landings; remote publication and destructive
  cleanup need separate maintainer authorization.

## Integration and validation

Commit coherent local steps; group them into a useful tested integration
result. Do not wait for a whole research milestone, or hand off every helper.
Rebase after relevant shared-contract changes and when needed for fast-forward
integration; batch unrelated main advances at the next integration boundary.
Never merge main into a feature branch or rewrite another agent's branch.
If main advances during review, preserve the reviewed object and arrange one
refreshed checkpoint. Root alone lands with `git merge --ff-only`.

Use Lean Beam for Lean iteration and focused checks for local steps.
At an integration candidate, run:

- `git diff --check` and `make check`;
- for Wasm/Talos code or proofs, `make talos-check` after worktree-local
  `make talos-setup`, plus the focused `lake build` proof cone;
- for W7 artifacts, `bash integration/talos/artifact/check.sh`
  (browser checks through `FIR_BROWSER`).

Documentation-only successors need not rebuild unchanged Talos code: cite its
last checked commit separately, never as fresh exact-head evidence. Full gates
belong at consumable checkpoints, not after every lemma or status message.
A suspected semantic discrepancy gets a `bugs/` card before a workaround.

Make/tooling commands are concise by default; `FIR_VERBOSE=1` gives live output.
Failures retain logs under `.deps/tool-logs/`; one-offs may use
`bash scripts/quiet-run.sh <label> -- <command...>`. GitHub Actions is the durable
validation record; local receipts/build outputs are disposable working state,
not an approval registry. `make check` refreshes scratch and cleans on success;
use `FIR_KEEP_VALIDATION=1` only for a specific investigation. No handoff requires
retaining historical binaries/traces.

## Handoff

A clean handoff reports outcome, exact base/head and contract base, lane,
changed files/contracts, checks/results, bug cards (or none), and follow-ups.
Keep it review-sized: one line per check family; link large evidence by path
and digest. Do not repeat header facts, inventories, JSON or command transcripts.
State the exact failing symbol/invariant inline when blocked.

An exact clean mailbox checkpoint is sufficient; no duplicate status-only
commit is required. Keep enduring design/results in the relevant tracked docs.
A tracked `ready` snapshot with `clean-at-update: false` is invalid.

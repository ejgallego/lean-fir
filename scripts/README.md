# FIR scripts

Repository-local validation and coordination entry points live here. Build
and validation tasks use the root `Makefile`; operational coordination uses
the mailbox CLI directly.

## Agent mailbox

- `scripts/mailbox check` validates immutable protocol messages and thread
  state in the primary checkout's canonical `.fir-mailbox/`.
- `scripts/mailbox list` gives a compact actionable work list. Add `--for
  <address>` to select a lane, `--verbose` for its latest checkpoint, or
  `--state completed` to review work awaiting closure.
- `scripts/mailbox deliver /path/to/message.md` validates and atomically
  publishes one complete draft, resolves its stable recipient through the
  canonical mailbox's local route registry, and automatically invokes
  `codex queue` by default. Missing/stale routes and queue failures warn while
  preserving successful authoritative delivery.
- `scripts/mailbox route bind|list|unbind` manages stable mailbox-address to
  exact Codex-session routes. Exact names must resolve uniquely; UUIDs avoid
  duplicate-name ambiguity.
- `--no-notify` skips route lookup and queueing when circumstances require it;
  `--notify-session <UUID or exact name>` directly overrides route lookup for
  one delivery.
- `make mailbox-test` runs the dependency-free parser, state-machine,
  atomic-delivery, routing, default-notification, worktree-resolution, and CLI
  contract tests.

The `mailbox-check`, `mailbox-list`, and `mailbox-deliver` Make targets remain
compatibility aliases during the transition.

The implementation was adapted from Lean VIR commit
`c8b0bdf8072521412d5a2cf0e1af1cc1e774f962`. FIR-specific policy and the
tracked `coordination/` boundary are documented in
`docs/MAILBOX_PROTOCOL.md`.

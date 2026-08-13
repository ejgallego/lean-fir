# FIR scripts

Repository-local validation and coordination entry points live here. The root
`Makefile` remains the normal command surface.

## Agent mailbox

- `make mailbox-check` validates immutable protocol messages and thread state
  in the primary checkout's canonical `.agents/mailbox/`.
- `make mailbox-list` lists active threads and their latest lane checkpoint.
- `make mailbox-test` runs the dependency-free parser, state-machine,
  worktree-resolution, and CLI contract tests.

The implementation was adapted from Lean VIR commit
`c8b0bdf8072521412d5a2cf0e1af1cc1e774f962`. FIR-specific policy and the
tracked `coordination/` boundary are documented in
`docs/MAILBOX_PROTOCOL.md`.

---
id: FIR-BUG-wasm-none-resident-arena-released-block-reuse
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-02
reproduction: integration/vbp-verso-viewer/check.sh
regression: none
---

# Summary

The resident allocator never reuses canonically released blocks, so one real
VBP ready-document render advances the monotonic frontier beyond 4.1 GiB and
the first retained-root update exhausts Wasm32 memory.

## Minimal reproduction

Mount the exact FLT `Preview.ready` payload from mailbox event
`VBP-FIR-20260902-001` through the accepted VBP widget package and VIR's real
browser/React host bindings. Wait for the render and snapshot effects to
commit, toggle the Follow cursor state, then mount the edited payload through
the same retained root.

## Exact commands

The external acceptance campaign is:

```sh
FIR_VBP_VERSO_VIEWER_PACKAGE=/absolute/path/to/vbp-verso-viewer-current \
  node scripts/vir_preview_browser_smoke.mjs
```

The FIR package gate will gain a bounded released-block reuse regression before
this card is resolved.

## Expected semantics

Lean's reference-counting runtime releases temporary constructor, closure,
string, Array, and numeric objects during rendering, and its allocator may
reuse compatible released storage. A persistent component root must retain its
live closures and host-resource handles, but dead render temporaries must not
consume a fresh Wasm32 address range forever.

## Actual behavior

`fir_release_header` marks dead allocations canonically freed, while
`fir_heap_alloc` only bumps the frontier. After the initial ready document has
committed, the next top-level mount begins at frontier `4,137,437,360`. During
the first edited component callback, the frontier reaches `4,294,967,256` and
memory reaches 65,536 pages. The allocator's failed `memory.grow` guard traps
with `unreachable`.

At the trap the retained component closure is still live and unchanged:
kind `closure`, flags `live`, reference count `1`, allocation bytes `48`.
There are 43,590 host-resource handles and 176 live callback roots. This
separates allocator exhaustion from closure-dispatch or callback-borrowing
failures.

## Proof or differential evidence

Interpreted VIR completes the original payload plus ten alternating edits.
The FIR top-level update itself returns successfully; the trap occurs in the
subsequent synchronous React component callback. The borrowed-bridge
regression independently invokes one retained callback twice without changing
its live header, but the real committed render still reaches the Wasm32 ceiling.

## Semantic impact

Long-lived browser packages cannot execute allocation-heavy retained
components even when reference counting identifies dead objects correctly.
The same monotonic-address-space limit applies to other persistent FIR-native
workloads; dropping the instance remains the only complete reclamation path.

## Classification and triage

This is generic resident-runtime fidelity debt. A repair should reuse storage
only after the ordinary resident release path has established a canonical dead
block, preserve persistent/live objects and pointer identity, and remain
compatible with explicit frontier rewinds. Application-specific instance
restarts or arbitrary graph persistence would hide rather than repair the
allocator mismatch.

## Workaround

None suitable for the retained component contract.

## Upstream tracking

none

## Resolution and regression

unresolved

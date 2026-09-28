# wasm-gen lane

Tracked frozen UTF-8 adapter producer, ROOT-W7-20260922-010.
Root remains integration owner; consumer browser qualification and live adoption
remain outside this producer task.

```text
lane: wasm-gen
owner: fir/wasm-gen
branch: wasm/utf8-scratch-4341
worktree: .worktrees/wasm-utf8-scratch-434
state: ready
base: dd688e3d9883731e81dd40f360a8241e9f290093
functional-head: 65cee114a9aa670f7a02ec33497d126cb63b6330
contract-base: dd688e3d9883731e81dd40f360a8241e9f290093
clean-at-update: true
slice: Promote accepted UTF-8 depth-scratch host, focused controls and frozen-input immutable producer under integration/vbp-native-session-probe/adapter.
files: integration/vbp-native-session-probe/adapter/; probe README; this snapshot
contracts: none; no Lean capture, Wasm, ABI, layout, runtime, W6 or toolchain change
checks: Functional head passes deterministic package replay, complete checksums, 22 equivalences/20 React SSR renders/1314 encodeInto calls, growth/reentry/failure/retention/disposal controls and five negative controls. git diff --check, make check, make talos-setup/check, and full deterministic artifact gate pass. No browser/performance campaign claimed.
bug-cards: none
blockers: none
handoff: Exact clean checkpoint and immutable package identity are recorded in the canonical completion. No VBP/live pin, publication, main change or push.
next: Root review/integration; queued Nat remainder remains a separate task.
```

The accepted host and smoke are byte-identical to package
`b5b3a053e4135f913504a376`. The input package
`1c3b87b3f270114a3a56eeb7` is authenticated by its complete checksum inventory,
BUILD and Wasm hashes before output is created. Twenty-one unchanged support
files are verified exactly. No mutable VBP/VIR source is consulted.

Wasm remains 1,981,006 bytes,
`b70d5b37c7954883a7e456821b7f6d4d31e0ef5903f77ff25c240a9b9f077d87`,
with 38 function imports, zero memory imports, 105 exports and module-owned
memory. BUILD retains the original RC2 compilation provenance and separately
records this 4.34.1 packaging checkout and exact producer-source hashes.

The producer uses the existing immutable-package utility without moving a
current pointer. Reproduction and source/ownership boundaries are documented in
`integration/vbp-native-session-probe/adapter/README.md`; final local packages
are under this worktree's `.deps/utf8-adapter/packages/`.

The old RC2 branch/checkpoint `05671f39` is unchanged. Its local generated Talos
state was preserved at `.deps/talos-rc2-preserved-05671f39/` after the stable
setup correctly rejected its old toolchain identity; fresh 4.34.1 setup passes.
No stale RC2 oleans or frozen renderer captures were used by the current gates.

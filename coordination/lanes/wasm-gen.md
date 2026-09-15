# wasm-gen lane

Current slice: `ROOT-W7-20260915-029`. The bounded trusted-local worker and
two-module assembly fixture is ready for root review. Root owns integration;
W7 stops before wider worklist continuation or lowering.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 7c5cacd681b1884de56924acd45447ccb354ff0c
functional-head: fb08ada2c1e524bd859df3aec5ad130681005ec0
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Reuse the accepted upstream object transport to assemble exactly the real renderer and isolated Basic selected closures; preserve renderer capture, check exact frontier and native-image isolation.
files: integration/vbp-native-session-probe/{ProductTransport.lean,product-transport-check.mjs,product-transport-check.sh,TWO_MODULE_WORKER.md,README.md}; coordination/lanes/wasm-gen.md
contracts: none; fixture/report only, no production compiler/source/plugin/runtime/W6/ABI/toolchain/consumer or package change
checks: Lean Beam sync version 4 zero diagnostics, stopped before final batch; exact functional-head product-transport-check.sh --assemble and default transport regression both pass 629-job cone/direct Lean and two producers/two consumers, exact blob and assembled declaration equality, original-root preservation, source hashes, 158/45 inventory, identity/body/interface/owner/merge negative controls and native maps; exact functional-head make check passes 730 cases/2172 comparisons, source-trust checks and 232 active cards; Node/bash syntax and base-to-final diff checks pass. Status successor changes this document only. No Talos/artifact/browser acceptance claimed for fixture-only scope.
bug-cards: none new; FIR-BUG-wasm-none-module-product-extension-registration remains open for production capture
blockers: none for requested two-module fixture; general worker integration/full closure is separately scoped
handoff: Clean immutable local-only checkpoint in canonical completion. Root review only; no main advance, push or package publication by W7.
next: Stop after exactly two requested entry closures. No recursive worklist, cache/durable format, lower/link/Wasm or runtime changes.
```

## Result

The renderer contributes 151 bodies / 41 signatures, Basic seven bodies / six
signatures. The assembly contains 158 bodies / 45 remaining signatures. Two
shared external interfaces deduplicate after signature and implementation-metadata
agreement. The selected Basic entry is not an immediate renderer import; this
is explicitly the requested two-entry composition, not the missing intermediate
dependency modules.

Root LCNF SHA-256 stays
`819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073`.
Combined LCNF SHA-256:
`8753415f035416839614b9596472b0a13dcd5c939a4f9300d7b6908a1446953d`.
Both clean functional-head producer blobs are 2,365,200 bytes, SHA-256
`86753ad894311159ba0fb68a1601717f9430e1bcf55760dbf03ebc05f81d28f7`.
Blob identity includes exact fixture/source provenance, so a later commit or
relocation may change the blob digest; identical-input repeats must match.

All original 41 signatures remain. The four additional ones are
`Lean.JsonNumber.fromNat`, `Array.toList`,
`List.foldl._at_.Array.appendList.spec_0._redArg`, and `Lean.Json.mkObj`.
These are source-level interfaces, not final Wasm imports.

Basic children map standalone Ext without the Manual aggregate. Renderer
assemblers map only the aggregate, unchanged through reads and assembly.
No registry reset, plugin editing, Environment transfer or initializer
suppression occurs. The accepted trusted-local, same-schema/toolchain unsafe
compactor boundary is unchanged; loaded regions remain allocated through
process exit. This is not an untrusted or durable interchange API.

## Evidence and remaining scope

Report: `integration/vbp-native-session-probe/TWO_MODULE_WORKER.md`.
Reproduce: `bash integration/vbp-native-session-probe/product-transport-check.sh --assemble`.
Exact input identities, full remaining signature rows, source text and repeats:
`.deps/native-session-probe/two-module-worker/`.
Logs: `.deps/native-session-probe/control/worker-committed-{final,transport,make-check}.log`.

Isolated Lean remains 4.34.0-rc2 at
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR remains 4.33.
The earlier 26-module / 1,201-body worklist is not resumed. No complete renderer
closure or Wasm result is claimed. Prior lifecycle/transport reports remain
in this fixture directory.

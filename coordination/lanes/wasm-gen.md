# wasm-gen lane

Current investigation: `ROOT-W7-20260915-031`, continued by root events `-032..033`
and the native-provider decision on main `ee4f8060`.
The full Lean-name source traversal and base lowering checkpoint is ready for
integration. The investigation remains active: the next generic FIR gap is
native-symbol resolution to upstream Lean export providers.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: ee4f80608c20a345d7bf50616ebd1f481af0d36b
functional-head: a6f138cc1b6cd49f70ce07053534658b1e7a94f1
contract-base: ee4f80608c20a345d7bf50616ebd1f481af0d36b
clean-at-update: true
slice: Complete the original renderer owner worklist with trusted-local isolated compiler products, lower its exact assembled LCNF, and identify unresolved native/VIR symbols and actual Lean export providers.
files: integration/vbp-native-session-probe/{ModuleProduct.lean,LowerModuleProduct.lean,module-product-worker.mjs,module-product-check.mjs,module-product-check.sh,README.md}; two W7 bug cards; coordination/lanes/wasm-gen.md
contracts: none; no production compiler/runtime, ABI, W6, toolchain, consumer or package-pointer change
checks: module-product-check.sh --isolated --lower passes the 630/51-job cones, direct Lean checks, two fresh owner traversals, exact source/metadata/compacted-byte equality, original-root/native-image preservation, independent Node base-Wasm validation, identical base bytes and strict link diagnostics, and twelve exact native/export signature matches. make check passes 730 cases/2172 comparisons and 234 bug cards. make talos-check passes 3205 jobs and forced trust audit. integration/talos/artifact/check.sh passes. Beam ModuleProduct version 4 and LowerModuleProduct version 3 have zero diagnostics; stopped before final batch. Node/bash syntax and diff-check pass. Gates ran on 008d111b's content; the final focused gate completed after that commit. Rebase onto coordination-only main ee4f8060 changes no fixture/bug-card content (git diff verifies equality); final diff/syntax/card checks pass. No browser or renderer execution acceptance claimed.
bug-cards: FIR-BUG-wasm-none-module-local-extern-frontier (fixed); FIR-BUG-wasm-none-native-export-source-provider (confirmed)
blockers: strict resident linking retains one large Nat literal, fifteen native externs and twelve intended VIR hosts; twelve native externs actually have upstream Lean export providers, so resolve that generic linking gap before considering replacement runtime implementations
handoff: Root may review/land the immutable clean checkpoint; main unchanged by W7, no push or package publication. This is not terminal completion of the broader renderer investigation.
next: Resolve actual C extern symbols against unique upstream export metadata, capture providers in their real owning modules and check compiled interfaces before linking; continue traversal. Genuine unprovided runtime/host requirements remain explicit and coordinated.
```

## Result

The original renderer now reaches 47 modules, 1,506 bodies and 138 source
selections. All remaining 125 signatures have native or VIR metadata: there are
no pending Lean-name edges. This is not yet complete native-symbol closure.
The first worker bug was distinguishing module-local extern implementations
from upstream's separate imported-signature list; classification now follows
the actual declaration value, without named exceptions.

The existing FIR lowerer emits a valid 777,173-byte base Wasm module, SHA-256
`4a025e1c9adafb34065f962368b5c27f15b218990c72f7660dd4fb895f2c30d0`.
Strict resident admission fails consistently. The diagnostic open view is not
published or executed as an accepted artifact. Its 28 imports comprise twelve
deliberate VIR host functions, literal `2^64`, `UInt64.ofNatLT`, and fourteen
String/Substring functions.

Actual upstream `getExternNameFor`/`getExportNameFor?` metadata identifies twelve
Lean providers among those String/Substring functions. All twelve compiled
interfaces agree exactly on types, borrows, safety and universe parameters.
Thus these are missing native-symbol source edges, not twelve runtime functions
to reimplement. No provider names are guessed from suffixes.

Durable report and exact source-product hashes:
`integration/vbp-native-session-probe/README.md`.
Disposable work: `.deps/native-session-probe/isolated-module-product/`.
Gate logs: `.deps/native-session-probe/control/closure-final-{focused,check,talos,artifact}.log`.
Isolated Lean remains 4.34.0-rc2 at
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR remains 4.33.
The accepted unsafe compactor remains same-toolchain/schema/trusted-local only;
all imported regions stay allocated through the assembler process lifetime.

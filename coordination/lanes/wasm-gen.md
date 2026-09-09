# wasm-gen lane

Generation roadmap: `Fir/Wasm/Emit/ROADMAP.md`. CG-05B was independently
accepted by root at `4366086b`. This is its separate, byte-neutral
production source-equation successor requested by W6.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 3ddb98e88788d0a02c1d03f577aa801dd905ce88
functional-head: 8e68650df0f2aafa4b7d5d7570c971d1e1464d61
contract-base: 3ddb98e88788d0a02c1d03f577aa801dd905ce88
clean-at-update: true
slice: Expose existing closure initializer fragments/local identities and six closed production source equations. Public-input partialApplicationFunction delegates to the unchanged checked private-key builder and is used by actual installation. No duplicate shadow implementation.
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ROADMAP.md}; this status
contracts: Additive proof-facing Lean source access only, authorized by W6-W7-20260909-008 and ROOT-W7-20260909-109. No instruction, runtime signature, layout, metadata, ownership, allocation, symbolic ABI, W6 file, root gate, toolchain or manifest change.
checks: git diff --check; both rebased patches identical by range-diff and stable patch IDs. Original Lean Beam update/sync/save (zero diagnostics) and clean 124-job build remain valid unchanged-source evidence; no new Lean edit. On exact 3ddb98e8 base: make check (730 cases, 2172 equal comparisons, 38 mailbox tests); make talos-check (3204 jobs, 3165-job cone, 52 forced trust endpoints); FIR_CHECK_JOBS=2 bash integration/talos/artifact/check.sh (complete deterministic/Node/adapter/checksum gates); final 124-job dependency cone and forced direct emitter/public importer. Talos setup is unchanged. Exact containing-head receipt is in the new authoritative update. Raw/optimized closure and prettyM Wasm/LCNF/manifest remain identical to accepted CG-05B and the retained pre-rebase package. No fresh browser or timing campaign.
bug-cards: none new; no semantic discrepancy or workaround
blockers: none for this source-equation handoff. W6 owns later byte-footprint/allocation refinement and remains separate.
handoff: Ready for standing fir/root to integrate the exact clean containing checkpoint from the new update on W7-ROOT-20260909-014, as requested by ROOT-W7-20260909-110. The original immutable completion remains unchanged; refresh includes only the patch-identical source-equation stack on root's reserved 3ddb98e8 default-only-case base and this status update. No W6 edit, main advance, push or external package-pointer move by W7.
next: W6 consumes the public equations for its reusable footprint proof after root integration. Keep return-node ABI census W6-W7-20260830-001 and deeper projection-owner/all-jump provenance W6-W7-20260831-006 separately queued; no further optimization bundled here.
```

## Public source boundary

The existing definitions `addressLocal`, `targetIdLocal`, `arityLocal`,
`captureId`, `zeroUnwrittenBytes`, `headerStores`, `captureStore`,
`captureStores`, and `typedAddressResult` are public without implementation
changes. `partialApplicationFunction` takes public descriptor-map/ordinal/
capture/result inputs; clients do not depend on the private `HelperKey`.

Maintained equations are `zeroUnwrittenBytes_eq`, `headerStores_eq`,
`captureStore_eq`, `captureStores_eq`, `typedAddressResult_eq`, and
`partialApplicationFunction_eq_ok`. The last exposes the exact parameter
ordering, sole local, allocator prefix, initialization fragments and suffix
under the existing checked-builder hypotheses.

The importer test uses these names and the successful-function equation
without privileged access to private names. Axiom inspection reports no
axioms for zero/header/result equations; capture/traversal use only
`propext`; the success equation uses only `propext` and `Quot.sound`.
No project-generated or native-evaluation axiom is introduced.

These are source equations, not memory-footprint, full allocation/capture
ownership, installed-helper or linker correctness theorems.
`FIR-BUG-wasm-none-partial-apply-tagged-result` remains open.

## Byte-neutral artifact

Immutable worktree-local package:

`integration/talos/artifact/_build/prettyM-current-releases/5b8addc4a5e8-f8f633fd679a1d0e`

This is the local `prettyM-current` target, with BUILD.json recording clean
rebased source `5b8addc4a5e88f722898f720cf1e9e6af656704f` (functional
`8e68650df0f2aafa4b7d5d7570c971d1e1464d61`). Wasm remains
**83,737 bytes**, SHA-256
`f8593cbb727e212b1846886145b35cd85b1503aea92149c53c115f4b01997f43`.
Byte identity preserves the 322 functions, 269 function exports, zero imports
and module-owned memory; capabilities/ownership and adapter are unchanged.
There is no runtime performance change claimed.

The closure fixture remains 5,128 raw / 2,980 optimized bytes, respectively:
`940922161c0d2226ea541cac80a60563b292aa41bd8878e3258aac5cc3e5ea1c`,
`d02d93d5b446eecb8e58d50e3cec57cebd4c9aff08feaa92ee20986aa6340f07`.
Existing poisoned-checkpoint and real release/reuse checks still pass.

Evidence: `.deps/cg05-equations/` contains the clean build/gate logs,
`Consumer.lean`, and `READOUT.md`; accepted CG-05B comparisons remain
in `.deps/cg05b/`. Root's separate acceptance of CG-05B and W6's narrow
footprint decision are not widened by these equations.

## Frozen-base refresh provenance

| Original commit | Rebased commit | Stable patch ID |
| --- | --- | --- |
| 468b86b6 | 8e68650d | 6309849f186591faad0e73e4bef4975340d33420 |
| 23a12abd | 5b8addc4 | 852f0dcc4ffefd9a816a1241ad1a7b86df2835bc |

This final handoff refresh changes only this mailbox document. New full-gate
logs are under `.deps/cg05-equations-rebase/`; the unchanged emitter and public
importer were also directly recompiled after the rebase. The original immutable
package `468b86b6c746-72be991f163fdf00` is preserved, not retargeted or overwritten.

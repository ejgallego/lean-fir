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
base: bd3761e5a0d5840fa14b40c80ddf4374901277bf
functional-head: 468b86b6c746abdf91568cf0cb7ec9e728860af3
contract-base: bd3761e5a0d5840fa14b40c80ddf4374901277bf
clean-at-update: true
slice: Expose existing closure initializer fragments/local identities and six closed production source equations. Public-input partialApplicationFunction delegates to the unchanged checked private-key builder and is used by actual installation. No duplicate shadow implementation.
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ROADMAP.md}; this status
contracts: Additive proof-facing Lean source access only, authorized by W6-W7-20260909-008 and ROOT-W7-20260909-109. No instruction, runtime signature, layout, metadata, ownership, allocation, symbolic ABI, W6 file, root gate, toolchain or manifest change.
checks: git diff --check; identical-patch range-diff after rebase; Lean Beam update/sync/save with zero errors/warnings; stop Beam, lake clean Fir, clean 124-job artifact/prettyM dependency build; forced direct emitter and external importing Consumer.lean; make check (730 cases, 2172 equal comparisons, 38 mailbox tests); make talos-check (3204 jobs, 3165-job cone, 49 forced trust endpoints); FIR_CHECK_JOBS=2 bash integration/talos/artifact/check.sh (complete deterministic/Node/adapter/checksum gates); final 124-job dependency cone. Talos setup already exists, unchanged. Exact containing-head receipt is in the authoritative completion. Raw and optimized closure bytes, prettyM Wasm/LCNF/manifest are identical to accepted CG-05B. No fresh browser or timing campaign.
bug-cards: none new; no semantic discrepancy or workaround
blockers: none for this source-equation handoff. W6 owns later byte-footprint/allocation refinement and remains separate.
handoff: Ready for standing fir/root to integrate the exact clean containing checkpoint from W6-W7-20260909-008 completion. Original base 4366086b was refreshed onto accepted W6 direct-let proof main bd3761e5 before full gates; patch is unchanged. No main advance, push or external package-pointer move by W7.
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

`integration/talos/artifact/_build/prettyM-current-releases/468b86b6c746-72be991f163fdf00`

This is the local `prettyM-current` target, with BUILD.json recording clean
functional source `468b86b6c746abdf91568cf0cb7ec9e728860af3`. Wasm remains
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

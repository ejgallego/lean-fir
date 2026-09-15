# wasm-gen lane

Current investigation: `ROOT-W7-20260915-031`, continued by root `-032..034`.
Native-export linking is ready for integration. Runtime closure and JS execution
remain separate unfinished parts of the continuous renderer investigation.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 5b73ec4303f4ce169ce03e69f07c62782ddd8c50
functional-head: fd77cba88a3efbd266f8308c9d2d6d6bee7309ef
contract-base: 5b73ec4303f4ce169ce03e69f07c62782ddd8c50
clean-at-update: true
slice: Generic native-symbol provider resolution, owning-module capture, ABI-exact forwarders, and the actual VIR host-boundary audit.
files: Fir/Wasm/Emit/NativeSymbol.lean; integration/vbp-native-session-probe capture/lowering drivers, native-symbol tests, input preparation, checker and README; native-export bug card; this lane status
contracts: none; no ABI/layout/runtime semantics, W6, toolchain, consumer source or package-pointer changes
checks: Two fresh captures and two lowerings agree on source/metadata/compacted bytes, base Wasm, strict-link report and host audit. module-product-check.mjs --isolated --lower --check-only validates those explicitly executed phases and current worker input hashes (not a fresh-generation claim). Final 4.34 dependency cone: 634 jobs; direct ModuleProduct/LowerModuleProduct pass. Generic module builds on 4.33 and 4.34; real extern/export rejection controls and emitted forwarding Node tests pass on both. Beam NativeSymbol v5, ModuleProduct v2, LowerModuleProduct v3, NativeSymbolTests v4: zero errors. make check: 730 cases/2172 comparisons; make talos-check: 3205 jobs plus forced audit; bash integration/talos/artifact/check.sh: pass. The final forwarding execution fixture was checked separately after the broad gates. Bug-card validation (234), syntax and diff-check pass. No browser or complete renderer execution acceptance claimed.
bug-cards: FIR-BUG-wasm-none-native-export-source-provider (fixed)
blockers: strict resident admission retains Nat literal 2^64, String.Internal.atEnd, String.Internal.get, UInt64.ofNatLT, String.Pos.Raw.atEnd and 12 intentional VIR hosts
handoff: Root owns review and main landing. This clean vertical checkpoint is not terminal completion. No W7 push/publication.
next: Existing-layout literal/primitive coverage, then actual current JS adapter execution using existing resource/callback infrastructure. No String/Substring source-provider reimplementations or host fallback. No new W6 request for existing-contract consumption.
```

## Result

The real `VersoBlueprint.Experimental.VirPreview.Renderer.render` reaches 52
modules, 1535 bodies, 158 selections and 16 native-symbol links. The 128 pre-link
external interfaces include those 16 resolved source links. The strict-link
frontier shrinks from 28 to 17 imports: all twelve formerly missing Lean export
providers disappear. No exported Lean provider remains unresolved.

Providers come from actual upstream metadata and exact compiled signatures,
then actual code/export metadata in the owning capture. Importers may hide
implementation expressions; requiring imported `defnInfo` incorrectly rejects
real providers such as `containsImpl`. Linking uses the existing pre-encoding
transform hook with typed forwarders; original LCNF and call/closure identities
are retained. No instruction-pattern recovery or fallback-body compilation.

The additional source interfaces are `String.extract`, `UInt8.land` and
`String.Pos.Raw.atEnd`; only the last becomes an additional runtime gap.
The VIR audit records actual targets, markers, ABI and borrowing. Bool/Float
are scalar arguments; `Callback.ofUnary` transfers a retained closure. It is
explicitly `admitted: false`, `executed: false`.

Base Wasm: 839735 bytes, SHA-256
`b154b7169d63c3aa02098b0f5936f0dee4d2fa5cc40a234ffcfaa8d602a0af9b`.
Original renderer LCNF remains
`819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073`.
All source-product hashes and reproduction instructions are in
`integration/vbp-native-session-probe/README.md`.

Disposable results: `.deps/native-session-probe/native-provider-product/{first,repeat}`.
Logs: `.deps/native-session-probe/control/native-provider-*` and
`native-symbol-cone.log`. The default shell gate still generates fresh products;
validation-only mode makes no new capture/execution claim. Isolated Lean remains
4.34.0-rc2 at `6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR remains
4.33. Consumer/source pins and the trusted-local transport restriction are
unchanged. Root may consume the exact clean checkpoint in the canonical event.

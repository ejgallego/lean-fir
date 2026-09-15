# wasm-gen lane

Current slice: `ROOT-W7-20260915-027`. Process-isolated one-product transport
feasibility is complete and ready for root review. Root retains integration and
the decision to introduce a broader driver.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 9b5696e4aef69d26a086e781c88993eb0a1286eb
functional-head: c35754530099c3ff5533a51c8c05349eaee9bfd6
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Demonstrate exact trusted-local upstream CompactedRegion transport of actual VersoManual.Basic final LCNF into an isolated renderer context, without overlapping native plugins.
files: integration/vbp-native-session-probe/{ProductTransport.lean,product-transport-check.mjs,product-transport-check.sh,PRODUCT_TRANSPORT.md,README.md}; coordination/lanes/wasm-gen.md
contracts: none; no production compiler, source policy, plugin list, runtime/W6/ABI/toolchain/consumer or package change; no general driver or durable format
checks: Lean Beam fixture sync passes with zero diagnostics; exact functional-head product-transport-check.sh passes 629-job source cone, direct Lean, two fresh producer exports and two fresh renderer consumers, full-data equality, byte determinism, signature/owner/body/integrity negative controls and unchanged native-image inventories; exact functional-head make check passes 730 cases/2172 comparisons and 232 active bug cards; Node/bash syntax and base-to-head diff checks pass. Fixture/report-only scope: no Talos/artifact/browser acceptance claimed. Containing status successor changes this document only.
bug-cards: no new card; FIR-BUG-wasm-none-module-product-extension-registration remains open for the production pipeline
blockers: no blocker for this experiment; broader isolation and complete renderer source closure require root's separately bounded decision
handoff: Clean local-only immutable checkpoint in canonical completion. Review fixture/report only; no main advance, push or package publication by W7.
next: Stop at requested boundary; root decides whether to generalize a trusted-local capture worker. Do not resume full worklist or lower/link/Wasm.
```

## Result

Real Basic capture records 841 groups / 2,443 declarations. The selected
`Verso.Genre.Manual.instToJsonInline.toJson` product has seven local bodies and
six external interfaces. Both exports have exact size 2,365,200 bytes and SHA-256
`bc0a220abd5ae07f9e3cb2fc049214004d4394ad015847733260535edca545c5`
at the clean functional head above. The payload embeds source/fixture identity,
so relocation or a new head may change that digest; identical-input repeats
must match.

Lean's existing `CompactedRegion.save/read` preserves compiler data with
`allowClosures := false` and no dependency regions. No environment, executable
closure, native handle or plugin is transferred. The unsafe erased-type reader
is gated by exact locally generated schema/toolchain/source/setup/plugin/blob
identity; this is not an untrusted binary format or cross-version API.

Entry and external signatures are mandatory. Six non-public generated
definitions have no imported signature, as expected from upstream's public-only
signature export. Their complete declarations match the canonical owning
capture, and all owners match the renderer environment. A private-body mutation
is rejected, as are borrow, owner, inventory, duplicate and identity mutations.

Both producer processes map standalone `verso_VersoManual_Ext.so`, not the
aggregate. Both renderer consumers map only `libverso_VersoManual.so` before
and after reads/admission. The conflicting images never coexist in a tested
process. No registry reset or initializer suppression is used.

## Evidence and remaining scope

Report: `integration/vbp-native-session-probe/PRODUCT_TRANSPORT.md`.
Exact input identities, inventories and repeated results:
`.deps/native-session-probe/transport/{identity.json,summary.json}`.
Final logs: `.deps/native-session-probe/control/transport-committed-final.log`
and `transport-committed-make-check.log`.

Isolated Lean remains 4.34.0-rc2, revision
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR remains 4.33.
The earlier worklist remains incomplete at 26 modules / 1,201 bodies / 111
remaining signatures. Its lifecycle diagnosis is retained in
`integration/vbp-native-session-probe/EXTENSION_LIFECYCLE.md`; this experiment
does not silently repair or resume it. No renderer Wasm result is claimed.

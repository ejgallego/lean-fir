# wasm-gen lane

Current slice: `ROOT-W7-20260915-025`. The module-capture lifecycle diagnosis
is complete and ready for root review. No repair or continued renderer closure
is implemented; root retains integration and the next design decision.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: f7dfd06c5aac860c7562dfbfc7a2ef37984c2678
functional-head: f23f74118adadae144a12b5fea2a32456c01ebe3
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Isolate overlapping aggregate/per-module native plugin initialization with fresh/serial capture and plugin-only controls; retain exact source/setup/plugin identities and reduced reproducer.
files: integration/vbp-native-session-probe/{ExtensionLifecycle.lean,extension-lifecycle-check.mjs,extension-lifecycle-check.sh,EXTENSION_LIFECYCLE.md,README.md}; bugs/FIR-BUG-wasm-none-module-product-extension-registration.md; coordination/lanes/wasm-gen.md
contracts: none; no production capture/importer/reset changes, source/plugin mutation, toolchain change, runtime/W6/ABI change, closure transport or Wasm work
checks: Lean Beam read-only registry probe and diagnostic fixture sync pass with zero blocking diagnostics; exact functional-head extension-lifecycle-check.sh passes 629-job source cone, direct Lean, five controls twice in fresh processes with identical JSON, expected failure-step/registry/library/symbol assertions and unchanged input hashes; exact functional-head make check passes 730 cases/2172 equal comparisons and 232 active bug cards; Node/bash syntax checks and base-to-head diff check pass. Fixture/report-only scope: no Talos/artifact/browser acceptance claimed. Containing status successor changes this document only.
bug-cards: FIR-BUG-wasm-none-module-product-extension-registration (existing card classified, not repaired)
blockers: aggregate libverso_VersoManual.so and standalone verso_VersoManual_Ext.so initialize overlapping native code in one process; compatible image/process policy remains a separate decision
handoff: Clean local-only immutable checkpoint in canonical completion; review fixture/report only. No main advance, push or package publication by W7.
next: Stop. Root separately scopes a compatible native-image policy or process-boundary/product-transport design; no worklist resume or initializer suppression is authorized.
```

## Causal result

The actual renderer setup loads aggregate `libverso_VersoManual.so`; the actual
`VersoManual.Basic` setup loads standalone `verso_VersoManual_Ext.so`. Both
define `initialize_verso_VersoManual_Ext` and the inline/block extension storage
symbols. The aggregate registers both extensions before the standalone plugin
tries to register the same name again. Lean's documented overlapping-plugin
restriction applies; this is not a demonstrated new upstream compiler defect.

| Fresh process experiment | Result |
| --- | --- |
| Basic capture | Pass: 841 groups; requested entry 7 locals / 6 signatures |
| Renderer then Basic | Exact duplicate inlineExtensionExt diagnostic |
| Basic twice | Pass |
| Renderer plugin list twice | Pass |
| Renderer plugin list then standalone Ext | Same duplicate, without any source capture |

Each row was repeated independently; full observation JSON matches. Registry
counts stay one after duplicate rejection. Read-only process maps identify the
two loaded images. Native generated-C guards are file-local, not a process-wide
module identity registry. No 26-module prefix or interpreted replay is needed.

The earlier module product remains 26 captures / 1201 bodies / 111 signatures
(74 primitive, 12 VIR, 25 source pending). It was not resumed.

## Evidence

Report and reproducer: `integration/vbp-native-session-probe/EXTENSION_LIFECYCLE.md`.
Exact identities and observations:
`.deps/native-session-probe/lifecycle/{inputs.json,summary.json,first/,repeat/}`.
Final logs: `.deps/native-session-probe/control/lifecycle-committed-final.log`
and `lifecycle-committed-make-check.log`.

Lean remains isolated 4.34.0-rc2 at
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; production FIR remains 4.33.
All frozen consumer sources and actual Lake setups are unchanged. No consumer
build products, system /tmp, registry reset, suppression or closure injection.

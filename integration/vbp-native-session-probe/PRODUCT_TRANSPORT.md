# Process-isolated compiler-product transport

## Result and boundary

The bounded `ROOT-W7-20260915-027` experiment demonstrates an existing,
lossless **trusted-local** transport for one actual `VersoManual.Basic` final
LCNF product. It uses Lean's `CompactedRegion.save/read`, not a new LCNF
serialization language. Two fresh producers and two fresh renderer-context
consumers agree. No production compiler, source policy, plugin list, runtime,
W6 definition, package or toolchain pin is changed.

This is not yet a process-isolated compiler driver, durable product format,
complete renderer closure, or Wasm result. The full module worklist is not
resumed. Root owns the decision to introduce a broader isolation boundary.

## Reproduce

```sh
bash integration/vbp-native-session-probe/product-transport-check.sh
```

The script prepares the existing pinned source views, checks the 629-job
`Fir.Wasm.Emit.ModuleSource` / renderer cone and directly checks
`ProductTransport.lean`, then runs the four fresh processes. All scratch and
outputs are under `.deps/native-session-probe/transport/`, never system `/tmp`.
`identity.json` records exact inputs and `summary.json` records blob SHA-256,
byte length, declaration inventory and both consumer results. The digest
includes the embedded source/fixture identity: it is deterministic across the
two exports for identical inputs, not invariant across commits or relocations.

## What is transported

The real source is captured using its unchanged Lake setup with isolated Lean
4.34.0-rc2, revision `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
The consumer sources remain the pins recorded by `prepare.mjs` / `SOURCE.json`.
Production FIR remains on its existing toolchain.

The fixture-local `Product` contains module/entry identity, the actual 841
final-LCNF groups (2,443 declarations), the selected 13 declarations, six
external names and selected owner rows. Selection uses the existing upstream
dependency traversal through `CapturedModule.artifact`; it is not a list of
invented generated-name seeds. The selected root is
`Verso.Genre.Manual.instToJsonInline.toJson`, with seven local bodies.

No `Environment`, native function closure, library handle or dependency region
is transported. `allowClosures := false` selects upstream's ordinary object
compaction path. Dependency regions are empty and loaded regions remain live
until process exit. The complete compiler data is preserved, including bodies,
types, parameters, borrow bits, names, recursion and inline metadata. Producer
readback and independent consumer reads use upstream structural `BEq` over the
entire product; byte equality is additionally required between fresh exports.

## Verification and public/private distinction

Before each typed-but-runtime-erased read, the launcher checks the exact Lean
revision, fixture schema source hash, source/setup/plugin hashes, embedded
source provenance, blob size and SHA-256. Producer and consumer are children
of this one launcher, using the same type definition and toolchain. This is
integrity checking of this experiment's own products, not authentication of
third-party binaries. `CompactedRegion.read` is unsafe and does not validate an
arbitrary blob's Lean type. Do not expose this fixture as an untrusted import API
or claim portability across toolchain/schema versions.

After transport the consumer requires unique declaration names, exact external
inventory, owner agreement with the renderer context and complete equality of
each selected local declaration with its canonical owning capture. The entry
and all six external dependencies must have matching imported signatures
(name, result type, universes, safety, ordered parameter types and borrow bits).
Parameter-local IDs/names are compilation-local, not the imported calling ABI.
Any additional available imported signature must also agree.

The first strict prototype required imported signatures even for private
implementation declarations and rejected a generated closed constant. Lean's
`LCNF.PhaseExt.mkSigDeclExt` exports only `isDeclPublic` signatures. The final
fixture therefore permits absent imported signatures **only** for non-public
owned internal definitions, whose complete declaration is checked. Public,
entry and external signatures remain mandatory. This mirrors the earlier
module-product distinction between canonical bodies and external interfaces;
it is a fixture correction, not a production admission relaxation.

The six private definitions are:

- `Verso.Genre.Manual.instToJsonTag.toJson._closed_1`
- `Verso.Genre.Manual.instReprPartMetadata.repr._redArg._closed_22`
- `Lean.Option.toJson._at_.Verso.Genre.Manual.instToJsonPartMetadata.toJson.spec_3`
- `Verso.Genre.Manual.instToJsonDomains._lam_2._closed_2`
- `Verso.Genre.Manual.instToJsonPartMetadata.toJson._closed_0`
- `_private.Init.Data.List.Impl.0.List.flatMapTR.go._at_.Verso.Genre.Manual.instToJsonPartMetadata.toJson.spec_5`

The six external interfaces are:

- `Lean.Name.toStringWithToken._at_.Lean.Name.toString.spec_0`
- `Lean.JsonNumber.fromNat`
- `Array.mkEmpty`
- `Array.toList`
- `List.foldl._at_.Array.appendList.spec_0._redArg`
- `Lean.Json.mkObj`

Negative controls reject altered toolchain/schema/blob identity before loading;
and altered embedded identity, owner, borrow signature, private body, external
inventory and duplicate selection at admission. No malformed binary is fed to
the unsafe upstream reader.

## Native lifecycle evidence

Both Basic producers load standalone `verso_VersoManual_Ext.so` and do not map
aggregate `libverso_VersoManual.so`. Each renderer consumer maps the aggregate
only; its complete VersoManual image inventory is unchanged by both reads and
verification. The observation uses `/proc/self/maps`, not just a requested
plugin list. The conflicting images never coexist in any tested process.

This avoids the lifecycle collision identified in
[EXTENSION_LIFECYCLE.md](EXTENSION_LIFECYCLE.md) without resetting extensions,
changing plugins, suppressing initializers or copying source. Existing card
`FIR-BUG-wasm-none-module-product-extension-registration` remains open for the
production multi-module pipeline: this fixture is feasibility evidence only.

## Acceptance scope

Lean Beam checks the fixture with zero diagnostics; the final batch cone,
direct Lean, repeated transport/negative controls, `make check` and
`git diff --check` are the applicable gates. Exact run/head results accompany
the W7 handoff. No Talos, linked artifact or browser acceptance is claimed for
this fixture/report-only slice. No performance claim is made.

The next decision is whether root wants a bounded source-capture worker using
this same-toolchain, trusted-local mechanism. Such a driver needs explicit
input closure identity, lifetime, failure handling and cache policy; none is
silently established by this single-product probe.

# Trusted-local two-module worker and assembler

## Scope and result

`ROOT-W7-20260915-029` advances the accepted
[transport probe](PRODUCT_TRANSPORT.md) to actual two-module source assembly.
It reuses the same fixture, upstream object compactor and input verification;
there is no second serializer, production driver or durable product format.

The entries are the real
`VersoBlueprint.Experimental.VirPreview.Renderer.render` and
`Verso.Genre.Manual.instToJsonInline.toJson`. The latter is the previously
blocked Basic selection from the wider worklist. It is not a direct import of
the original renderer closure: this bounded test combines the two requested
entry closures, not the intervening dependency modules.

| Source product | Bodies | External signatures |
| --- | ---: | ---: |
| Original renderer entry | 151 | 41 |
| Selected Basic entry | 7 | 6 |
| Combined, exactly two modules | 158 | 45 |

The original renderer LCNF stays byte-identical, SHA-256
`819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073`.
The combined LCNF is deterministic, SHA-256
`8753415f035416839614b9596472b0a13dcd5c939a4f9300d7b6908a1446953d`.
These source-text hashes are asserted independently of the transported blob's
identity-dependent digest.

## Running the bounded worker

```sh
bash integration/vbp-native-session-probe/product-transport-check.sh --assemble
```

The existing launcher starts two fresh Basic producer processes and two fresh
renderer assembler processes. Each Basic worker uses its unchanged real source
and Lake setup, captures 841 groups / 2,443 final declarations, selects the
requested closure using upstream collection, and exports a CompactedRegion.
Each assembler captures the real renderer in its own unchanged native context,
reads both validated products, checks them, and constructs the combined FIR
source artifact. No Basic environment or native library is transferred.

The default command without `--assemble` retains the earlier transport-only
gate. Every run produces fresh compiler products; there is no cache reuse.
All outputs and temporary files are worktree-local under
`.deps/native-session-probe/two-module-worker/`.

## Verification and ownership

The trusted launcher checks exact source/setup/plugin, toolchain, schema and
blob identities before unsafe decoding. Full declaration/body/interface/owner
checks occur after decoding and before source-product admission. No claim is
made that an erased-type object reader can inspect bodies before reading them.
The same-toolchain/schema, locally produced input boundary from the accepted
probe is unchanged. Regions are not freed during use; they remain allocated
until the short-lived assembler process exits. There is no cross-process
pointer, Environment or native closure sharing.

The assembler requires canonical full-body agreement and exact owner identity
for both modules. Duplicate body providers fail. Shared external declarations
must agree in calling signature and external implementation metadata. Resolving
an external to a local body requires matching signature and an opaque source
boundary, not a native operation. The existing checks for absent public
interfaces and non-public generated definitions remain intact.

Both independent products must yield identical complete declaration arrays,
external inventories, report JSON and formatted source. The original renderer
declarations and signatures must remain structurally equal after assembly.
The two entries must remain local bodies. Negative controls additionally reject
a wrong renderer provider, changed borrow annotation and conflicting external
metadata, alongside the accepted transport/integrity/body controls.

Each Basic process maps standalone `verso_VersoManual_Ext.so`, not the Manual
aggregate. Each assembler maps only aggregate `libverso_VersoManual.so`, both
before and after reads and assembly. `/proc/self/maps` checks show no overlapping
aggregate/standalone Manual images in any tested process. No initializers are
suppressed, plugins changed, or persistent extensions reset.

## Exact remaining interfaces

All original 41 renderer signatures remain unresolved. Two Basic signatures
already occur in that list and are deduplicated only after exact agreement:
`Array.mkEmpty` and
`Lean.Name.toStringWithToken._at_.Lean.Name.toString.spec_0`.
The four additional signatures, in deterministic append order, are:

- `Lean.JsonNumber.fromNat`
- `Array.toList`
- `List.foldl._at_.Array.appendList.spec_0._redArg`
- `Lean.Json.mkObj`

`first-assembly.json` and `repeat-assembly.json` record all 45 names in order,
plus owner, result type, ordered parameter types/borrow bits, safety and universe
parameters. Their `.product.lcnf` companions retain the complete symbolic
declarations. `summary.json` binds both repeats and their hashes; `identity.json`
records the exact source inputs. The launcher independently checks the expected
union-minus-bodies frontier, unique names, 158/45 counts and exact source hashes.
These are source signatures, not a claimed final Wasm import count.

## Handoff boundary

Only fixture/report and W7 lane status change. Lean Beam checks the source;
the final direct Lean / 629-job dependency cone, repeated transport and assembly
checks, default transport regression, `make check`, syntax and diff checks are
reported against the clean functional checkpoint in the handoff. No Talos,
linked artifact or browser result is claimed for this fixture-only slice.

The earlier production worklist remains incomplete at 26 modules / 1,201 bodies;
it is not resumed here. Existing
`FIR-BUG-wasm-none-module-product-extension-registration` remains open for the
production path. No new semantic discrepancy or workaround is introduced.
Lowering, linking, Wasm generation, general worker/caching policy, consumer
changes and any runtime/ABI/W6 work require separate scope from root.

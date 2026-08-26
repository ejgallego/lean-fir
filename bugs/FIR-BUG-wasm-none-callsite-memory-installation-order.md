---
id: FIR-BUG-wasm-none-callsite-memory-installation-order
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-27
reproduction: integration/talos/artifact/FirWasmSourceExample.lean
regression: none
---

# Summary

Resident `getTag` call-site specialization validates memory-using rewritten
functions before the generic internalizer installs the module-owned memory.

## Minimal reproduction

Compile the structured `prettyFormatRaw` source entry without attaching a
runtime invocation, then internalize only its semantic `getTag` operation. The
source module is valid without linear memory. The reviewed caller rewrite for
Lean's inline `lean_obj_tag` path introduces constructor-header `i32.load`
instructions before the resident helper transaction installs memory.

## Exact commands

From the repository root on the reported checkpoint:

```sh
FIR_PRETTYM_CHECKPOINTS=1 lake env lean \
  integration/talos/artifact/FirWasmSourceExample.lean
```

The complete gate enables the same path with:

```sh
FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 \
  bash integration/talos/artifact/check.sh
```

## Expected semantics

Generic resident linking must validate the untouched source module, apply its
reviewed call-site rewrites, install the selected helper and module-owned
memory as one transaction, and validate the completed output. The isolated
`getTag` checkpoint must be import-free for `getTag` and encode successfully.

## Actual behavior

`ResidentRuntime.internalizeGetTag` rewrites the source functions first and
then enters `internalizeOperation`, whose input validation observes the new
`i32.load` before memory is present. Validation fails with
`Fir.Wasm.SymbolicError.memoryInstructionWithoutMemory` in the specialized
`Std.Format.be` closure.

## Proof or differential evidence

Tooling reproduced the failure using both its candidate and the unchanged
parent artifact script, before the tooling-only source-isolation branch ran.
The normal artifact gate remains green because it does not validate this bare
intermediate checkpoint.

## Semantic impact

Any generic resident call-site rewrite that introduces a memory instruction
can reject an otherwise valid memoryless source module when the same resident
transaction is responsible for installing memory. Consumers whose source
module already owns memory conceal the sequencing defect.

## Classification and triage

This is a W7 resident-linker transaction-order defect. The `getTag` helper,
inline instruction sequence, ABI, and W6 representation contract are not in
question; only the order of generic validation, rewriting, helper/memory
installation, and final validation is wrong.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved


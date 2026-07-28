---
id: FIR-BUG-validation-none-execution-input-argmax
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 361b31b5c7aa05332519985ef0fc4fe9819c3d80
phase: validation
pass: none
discovered-by: differential-test
first-seen: 2026-07-28
reproduction: scripts/validation_harness.py
regression: scripts/test_validate_interpreters.py#test_external_execution_input_scales_beyond_execve_arg_max
---

# Summary

The generic external-adapter harness serializes every exposed execution
product twice into the child environment, so a sufficiently broad validation
corpus exceeds the operating system's `execve` argument-and-environment limit
before the real backend can run.

## Minimal reproduction

Run the native-oracle matrix with the 169-source-case corpus. The V8 adapter
receives 338 source/provider products. `ExternalCommandAdapter.execute`
serializes those products, including absolute paths, into
`FIR_VALIDATION_PRODUCTS` and serializes the complete provider bundle again
into `FIR_VALIDATION_PRODUCT_BUNDLE`.

## Exact commands

From the native-validation worktree:

```text
make check
```

The native-to-LCNF and direct tiers complete, but the V8 tier fails while
starting its opt-in `strace` recorder with:

```text
OSError: [Errno 7] Argument list too long: '/usr/bin/strace'
```

## Expected semantics

Corpus size must not determine whether the operating system can start a
backend. Large structured execution inputs should be retained as canonical
files, passed by short path bindings, and read by the backend under the same
file-access evidence used for generated products.

## Actual behavior

The harness copies the complete product inventory and provider bundle into
environment variables. Linux accounts both strings against `ARG_MAX`, and
`execve` rejects the recorder process before either the recorder or V8 can
observe the products.

## Proof or differential evidence

At 169 selected source cases the native oracle and LCNF interpreter agree on
all 169 results and all nine direct fixtures agree. Construction exposes 338
products to V8, but there is no V8 process log or semantic result because
process creation fails at the harness boundary.

## Semantic impact

The failure places a machine-dependent ceiling on validation coverage and can
silently turn added semantic signal into an infrastructure outage. It affects
every external adapter with a large product inventory, not just V8 or Wasm.

## Classification and triage

This is a validation-harness transport defect, not a Lean, LCNF, Wasm, V8, or
recorder semantic discrepancy. The generic adapter should materialize sealed
canonical execution-input files and expose only their paths.

## Workaround

None. Reducing the corpus, disabling the recorder, or splitting the matrix
would weaken validation and is not an accepted repair.

## Upstream tracking

None.

## Resolution and regression

The generic adapter now writes one canonical, read-only
`execution-input.json` containing the selected cases, exposed products, and
optional provider bundle, and passes only its absolute path through the
environment. The exact bytes are retained as an `execution-input` artifact
and cross-checked by the offline verifier; the live harness rejects content
mutation, replacement (including inode reuse), symlinks, and extra hard links.

`test_external_execution_input_scales_beyond_execve_arg_max` starts a real
subprocess with an execution-input artifact larger than the host's `ARG_MAX`.
`test_external_execution_input_rejects_tampering_and_symlinks` permanently
checks the fail-closed file identity boundary. The 169-case native/LCNF/V8
matrix then completed 507/507 pairwise comparisons with zero findings while
the opt-in recorder observed all 338 receipted products.

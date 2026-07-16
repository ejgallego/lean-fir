---
id: FIR-BUG-<phase>-<pass>-<short-slug>
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: <exact-revision>
phase: <base|mono|impure|wasm>
pass: <pass-name-and-occurrence-or-none>
discovered-by: <proof|differential-test|invariant-check>
first-seen: <YYYY-MM-DD>
reproduction: <repo-relative-path>
regression: none
---

# Summary

One sentence describing the semantic discrepancy.

## Minimal reproduction

The smallest program or fixture that exhibits the discrepancy.

## Exact commands

Commands that reproduce it from a clean checkout.

## Expected semantics

The expected FIR observation and why it is expected.

## Actual behavior

The observed compiler, interpreter, proof, or Wasm behavior.

## Proof or differential evidence

The failed obligation, trace difference, or violated invariant.

## Semantic impact

Which programs or correctness claims are affected.

## Classification and triage

Evidence for the current classification and any remaining uncertainty.

## Workaround

Temporary workaround, or `none`.

## Upstream tracking

Upstream issue or pull request, or `none`.

## Resolution and regression

Fixing revision and permanent regression test, or `unresolved`.

---
id: FIR-BUG-impure-alphaEqv-opaque-eqv
status: confirmed
classification: upstream-drift
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: simpCase-0
discovered-by: proof
first-seen: 2026-07-16
reproduction: Fir/LeanIR/Passes/AlphaEqvCode.lean#alphaEqvSoundAt_of_terminal_bridge
regression: scripts/validate_trusted_assumptions.py
---

# Summary

Lean 4.32 exposes the recursive LCNF alpha-equivalence checker as an opaque
`partial def`, preventing a kernel proof from inspecting a successful
`Code.alphaEqv` result even for terminal code.

## Minimal reproduction

For two return instructions, assume
`(.return leftId).alphaEqv (.return rightId) = true` and try to change that
hypothesis to `(leftId == rightId) = true`. Lean rejects the change because
`LCNF.AlphaEqv.eqv` is not definitionally reducible.

The compiled environment contains `LCNF.AlphaEqv.eqv` and its unsafe runtime
recursor, but no public equation or unfolding theorem analogous to the
equations exported for the non-partial helper functions.

## Exact commands

From a clean checkout using the pinned toolchain:

```sh
lean --version
rg -n "partial def eqv" \
  ~/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Compiler/LCNF/AlphaEqv.lean
lake build Fir.LeanIR.Passes.AlphaEqvCode
```

The failed proof probe is the attempted executable bridge described beside
`alphaEqvSoundAt_of_terminal_bridge`.

## Expected semantics

The proof should be able to use a public equation theorem for `eqv`, reduce a
successful check according to the constructors of the two code values, and
recover the corresponding declarative alpha relation.

## Actual behavior

`#print LCNF.AlphaEqv.eqv` reports an opaque constant. Simplification and
unfolding leave `ReaderT.run (LCNF.AlphaEqv.eqv left right) rho` unchanged, and
the environment exposes no safe public equation theorem for `eqv`.

## Proof or differential evidence

The terminal `return` proof cannot derive identifier equality from the
executable result. In contrast, FIR can prove the terminal declarative
relation sound and can prove executable soundness conditional on the missing
checker-to-relation bridge.

## Semantic impact

This does not demonstrate a wrong compiler transformation. It prevents FIR
from closing the proof boundary around the exact `Code.alphaEqv` Boolean used
by `simpCase`; without an upstream equation theorem or a verified replacement
checker, whole-pass correctness must retain an explicit bridge assumption.

## Classification and triage

This is classified as `upstream-drift`: the Lean implementation is executable
and may be semantically correct, but its current declaration form provides no
kernel-facing recursion principle suitable for downstream verification.

## Workaround

FIR ships a total, transparent, fuel-indexed copy of Lean 4.32's checker in
`AlphaEqvLocal.lean`. Semantic proofs target that copy and remain axiom-free.
`AlphaEqvTrusted.lean` contains one explicitly named axiom saying that every
successful upstream check has a finite accepting local run. The adapter
records the audited upstream source hash; `make check` verifies the pinned
toolchain, source hash, absence of other project axioms, and absence of a
replacement opaque `partial def`. Differential guards compare both checkers
over the interpreter regression corpus.

## Upstream tracking

none

## Resolution and regression

The upstream proof-interface problem remains unresolved. FIR's audited local
adapter makes the assumption usable and visible without blocking semantic
work. A complete resolution should expose a safe upstream equation theorem,
prove `UpstreamBridge`, and delete `lean432UpstreamBridge`.

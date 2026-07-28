# FIR semantic bug cards

Create a card as soon as a proof failure, differential mismatch, or invariant
violation indicates a possible semantic discrepancy. Do this before adding a
workaround. A new report starts as `candidate`; minimization and triage may
then classify it as a compiler, FIR-semantics, validation-harness,
Wasm-adapter, or upstream-drift issue.

Copy `_template.md` to a collision-resistant name of the form:

```text
FIR-BUG-<phase>-<pass>-<short-slug>.md
```

The phase and pass should use Lean's pass-manager spelling and include an
occurrence when relevant, for example `impure-pushProj-1`. Do not allocate
numbers from a central counter: independent interpreter, proof, and Wasm work
must be able to create cards without coordination.

## Lifecycle

- `candidate`: captured evidence has not yet been minimized or classified.
- `confirmed`: the discrepancy is reproducible and its owner is known.
- `upstreamed`: an upstream report or pull request is linked.
- `fixed`: a fixing revision and permanent regression test are linked.
- `closed-not-a-bug`: the behavior was shown to be intended; explain why.

Allowed classifications are `compiler`, `fir-semantics`,
`validation-harness`, `wasm-adapter`, and `upstream-drift`. A card remains in
the repository after resolution so that the evidence and regression-test
history are not lost.

`make bug-cards` validates frontmatter, headings, IDs, filenames, and local
reproduction/regression links. The template is validated structurally but is
not treated as an active report.

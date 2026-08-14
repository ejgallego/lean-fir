# Postponed source views

`postponed-source-view.mjs` builds only the private `.olean` replay surface for
one explicitly named source module. It does not ask Lean to finish unrelated
native IR; consumers prepend the returned path only while running FIR capture.

Run the focused contract with:

```sh
node --test integration/package-tools/postponed-source-view.test.mjs
```

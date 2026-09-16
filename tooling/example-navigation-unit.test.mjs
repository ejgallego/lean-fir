import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync, statSync } from "node:fs";
import { dirname, posix, resolve } from "node:path";
import test from "node:test";

// The two navigation pages use simple inline Markdown links. This is not a
// general Markdown validator or an artifact/consumer acceptance check. Remote
// URLs and anchors remain outside this offline, tracked-source boundary.
function localTargets(document, markdown) {
  return [...markdown.matchAll(/\[[^\]\n]*\]\(([^\s()]+)\)/g)]
    .map((match) => match[1])
    .filter((target) => !/^(?:[a-z][a-z0-9+.-]*:|\/\/|#)/i.test(target))
    .map((target) => posix.normalize(posix.join(
      posix.dirname(document), decodeURIComponent(target.split(/[?#]/)[0]),
    )));
}

function requireTracked(targets, tracked) {
  for (const target of targets) {
    assert(tracked.has(target), `missing or untracked navigation target: ${target}`);
  }
}

test("relative navigation resolves paths, percent encoding and fragments", () => {
  assert.deepEqual(localTargets("docs/index.md",
    "[policy](../integration/policy.json) [section](guide.md#section) " +
    "[space](guide%20name.md) [remote](https://example.org/a) " +
    "[mail](mailto:owner@example.org) [cdn](//example.org/a) [here](#here)"),
  ["integration/policy.json", "docs/guide.md", "docs/guide name.md"]);
});

test("missing, ignored-output and escaping targets fail rather than skip", () => {
  const tracked = new Set(["docs/guide.md"]);
  requireTracked(["docs/guide.md"], tracked);
  for (const target of ["docs/missing.md", "_build/package/BUILD.json", "../other/README.md"]) {
    assert.throws(() => requireTracked([target], tracked),
      /missing or untracked navigation target/);
  }
});

const root = resolve(dirname(import.meta.filename), "..");
const tracked = new Set(execFileSync("git", ["ls-files", "-z"],
  { cwd: root, encoding: "utf8" }).split("\0").filter(Boolean));

for (const document of ["docs/build-examples.md", "docs/package-build-client-map.md"]) {
  test(`${document}: local navigation uses present tracked source files`, () => {
    const targets = localTargets(document, readFileSync(resolve(root, document), "utf8"));
    assert(targets.length > 0, "navigation page has no recognized local links");
    requireTracked(targets, tracked);
    for (const target of targets) {
      assert(statSync(resolve(root, target)).isFile(), `not a source file: ${target}`);
    }
  });
}

test("make examples names present tracked Lean modules, without a second list", () => {
  const makefile = readFileSync(resolve(root, "Makefile"), "utf8").replace(/\\\n/g, " ");
  const recipe = makefile.match(/^examples:\n([\t ].*\n)+/m)?.[0];
  assert(recipe, "missing examples target");
  const modules = recipe.match(/\bFir(?:\.[A-Za-z0-9_]+)+\b/g) ?? [];
  assert(modules.length > 0, "examples target has no recognized Lean modules");
  requireTracked(modules.map((module) => module.replaceAll(".", "/") + ".lean"), tracked);
});

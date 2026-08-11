import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL, fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const packageRoot = resolve(process.argv[2] ?? join(directory,
  "_build/verso-html-current"));
const versoRoot = resolve(process.env.VERSO_ROOT ?? join(directory, ".verso"));
const adapterModule = await import(pathToFileURL(join(packageRoot,
  "prettyM-browser-adapter.mjs")));
const { PrettyFormat: F, createPrettyMAdapter } = adapterModule;
const bytes = readFileSync(join(packageRoot, "prettyM.wasm"));
const manifest = JSON.parse(readFileSync(join(packageRoot,
  "prettyM.wasm.json"), "utf8"));
const build = JSON.parse(readFileSync(join(packageRoot, "BUILD.json"), "utf8"));

const tagged = (tag, cssClass, binding = null) =>
  ({ tag, annotation: { cssClass, binding } });
const cases = [
  ["empty", F.nil(), [], 80, 0, 0],
  ["plain escape", F.text('α<&"'), [], 80, 0, 0],
  ["annotated escape", F.tag(5, F.text('α<&"')),
    [tagged(5, 'kw<&"', 'b<&"')], 80, 0, 0],
  ["nested sparse tags", F.tag(4, F.append(F.text("a"),
    F.append(F.tag(109, F.text("β")), F.text("c")))),
    [tagged(4, "outer"), tagged(109, "inner", "bind-λ")], 80, 0, 0],
  ["missing inner annotation", F.tag(7,
    F.append(F.text("a"), F.tag(8, F.text("b")))),
    [tagged(7, "outer")], 80, 0, 0],
  ["multiple end tags", F.tag(17, F.tag(29, F.text("x"))),
    [tagged(17, "a"), tagged(29, "b")], 80, 0, 0],
  ["indented newline", F.nest(7,
    F.append(F.text("a"), F.append(F.line(), F.text("b")))), [], 1, 2, 0],
  ["nonzero column", F.group(F.append(F.text("hello"),
    F.append(F.line(), F.text("world")))), [], 10, 3, 9],
];

const oracleText = execFileSync("lake", ["--keep-toolchain",
  `-KversoRoot=${versoRoot}`, "env", "lean", "--run", "Oracle.lean"], {
  cwd: directory,
  encoding: "utf8",
  maxBuffer: 32 * 1024 * 1024,
});
const expected = new Map(oracleText.trim().split("\n").map((line) => {
  const separator = line.indexOf("\t");
  return [line.slice(0, separator), JSON.parse(line.slice(separator + 1))];
}));

const adapter = await createPrettyMAdapter({ bytes, manifest, build });
for (const [name, format, annotations, width, indent, column] of cases) {
  const result = adapter.render({ format, annotations, width, indent, column });
  assert.equal(result.html, expected.get(name), name);
  assert.equal(result.timings.totalMs,
    result.timings.prepareMs + result.timings.executeMs + result.timings.decodeMs);
}
console.log(`native/Wasm HTML differential: PASS (${cases.length} cases)`);

{
  const growthAdapter = await createPrettyMAdapter({ bytes, manifest, build });
  const result = growthAdapter.render({
    format: F.tag(2, F.text("λ<&\"".repeat(512))),
    annotations: [tagged(2, "unicode")],
    width: 100000,
  });
  assert.ok(result.html.length > 8192);
  assert.ok(result.memory.pagesAfterExecute > result.memory.pagesBefore);
  console.log(`bounded growth: PASS; pages=${result.memory.pagesBefore}->` +
    `${result.memory.pagesAfterExecute}`);
}

{
  let lastFrontier = 0;
  for (let index = 0; index < 32; index += 1) {
    const result = adapter.render({
      format: F.tag(index + 1, F.text(`α-${index}`)),
      annotations: [tagged(index + 1, "token", index % 2 ? "b" : null)],
      width: 80,
      indent: index % 4,
      column: index % 7,
    });
    assert.ok(result.html.includes(`α-${index}`));
    assert.ok(result.memory.frontierAfterDecode >= lastFrontier);
    lastFrontier = result.memory.frontierAfterDecode;
  }
  console.log(`32 repeated calls: PASS; finalFrontier=${lastFrontier}`);
}

assert.throws(() => adapter.render({
  format: F.text("bad"),
  annotations: [{ tag: 1, annotation: { cssClass: 7 } }],
  width: 80,
}), /cssClass must be a string/);
assert.throws(() => adapter.render({
  format: F.text("bad"),
  annotations: [tagged(1, "a"), tagged(1, "b")],
  width: 80,
}), /duplicate tag/);
console.log("malformed annotation contract: PASS");

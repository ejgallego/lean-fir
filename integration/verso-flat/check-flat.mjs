import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL, fileURLToPath } from "node:url";

const directory = dirname(fileURLToPath(import.meta.url));
const packageRoot = resolve(process.argv[2] ?? join(directory,
  "_build/verso-flat-current"));
const versoRoot = resolve(process.env.VERSO_ROOT ?? join(directory, ".verso"));
const adapterModule = await import(pathToFileURL(join(packageRoot,
  "prettyM-browser-adapter.mjs")));
const { PrettyFormat: F, createPrettyMAdapter } = adapterModule;
const bytes = readFileSync(join(packageRoot, "prettyM.wasm"));
const manifest = JSON.parse(readFileSync(join(packageRoot,
  "prettyM.wasm.json"), "utf8"));
const build = JSON.parse(readFileSync(join(packageRoot, "BUILD.json"), "utf8"));

function balanced(depth) {
  if (depth === 0) return F.text("λ");
  const child = balanced(depth - 1);
  return F.append(child, child);
}

function groupedBreaks(count) {
  let result = F.text("x");
  for (let index = 0; index < count; index += 1) {
    result = F.append(result, F.append(F.line(), F.text("y")));
  }
  return F.group(result);
}

const cases = [
  ["empty", F.nil(), 80, 0, 0],
  ["nested tags", F.tag(4, F.append(F.text("α"), F.tag(9,
    F.append(F.text("b"), F.append(F.line(), F.text("γ")))))), 3, 0, 0],
  ["multiple end tags", F.tag(17, F.tag(29, F.text("x"))), 80, 0, 0],
  ["indented newline", F.nest(7,
    F.append(F.text("a"), F.append(F.line(), F.text("b")))), 1, 2, 0],
  ["nonzero column wide", F.group(F.append(F.text("hello"),
    F.append(F.line(), F.text("world")))), 20, 3, 9],
  ["nonzero column narrow", F.group(F.append(F.text("hello"),
    F.append(F.line(), F.text("world")))), 10, 3, 9],
  ["large tag", F.tag(1099511627779n, F.text("payload")), 80, 0, 0],
  ["balanced append", balanced(10), 80, 0, 0],
  ["unicode chunk", F.tag(3, F.text("α".repeat(131072))), 200000, 0, 0],
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

async function adapter(options = {}) {
  return createPrettyMAdapter({ bytes, manifest, build, ...options });
}

const differential = await adapter();
for (const [name, format, width, indent, column] of cases) {
  const result = differential.render({ format, width, indent, column });
  assert.deepEqual(result.rendered, expected.get(name), name);
  assert.equal(result.timings.totalMs,
    result.timings.prepareMs + result.timings.executeMs + result.timings.decodeMs);
}
console.log(`native/Wasm differential: PASS (${cases.length} cases)`);

{
  const instance = await adapter();
  const format = F.tag(7, F.text("α".repeat(524288)));
  const result = instance.render({ format, width: 2_000_000 });
  assert.equal(new TextEncoder().encode(result.rendered.text).length, 1048576);
  assert.deepEqual(result.rendered.events, [
    { offset: 0, kind: 0, value: 7 },
    { offset: 1048576, kind: 1, value: 1 },
  ]);
  assert.ok(result.memory.pagesAfterExecute > result.memory.pagesBefore);
  console.log(`1 MiB UTF-8: PASS; pages=${result.memory.pagesBefore}->` +
    `${result.memory.pagesAfterExecute}`);
}

{
  const instance = await adapter();
  const balancedResult = instance.render({ format: balanced(10), width: 80 });
  assert.equal(balancedResult.rendered.text, "λ".repeat(1024));
  const groupedResult = instance.render({ format: groupedBreaks(256), width: 16 });
  assert.equal(groupedResult.rendered.events.length, 256);
  assert.ok(groupedResult.rendered.text.includes("\n"));
  console.log("stack shapes: PASS; balancedNodes=2047; groupedBreaks=256");
}

{
  const instance = await adapter();
  let lastFrontier = 0;
  for (let index = 0; index < 32; index += 1) {
    const text = `α-${index}`;
    const result = instance.render({
      format: F.tag(index + 1, F.text(text)),
      width: 80,
      indent: index % 4,
      column: index % 7,
    });
    const textBytes = new TextEncoder().encode(text).length;
    assert.deepEqual(result.rendered, {
      text,
      events: [
        { offset: 0, kind: 0, value: index + 1 },
        { offset: textBytes, kind: 1, value: 1 },
      ],
    });
    assert.ok(result.memory.frontierAfterDecode >= lastFrontier);
    lastFrontier = result.memory.frontierAfterDecode;
  }
  console.log(`32 repeated calls: PASS; finalFrontier=${lastFrontier}`);
}

{
  let tick = 0;
  const instance = await adapter({ now: () => tick++ });
  const result = instance.render({ format: F.text("timed"), width: 80 });
  for (const phase of ["normalizeMs", "allocateMs", "encodeMs", "prepareMs",
    "executeMs", "decodeMs", "totalMs"]) {
    assert.ok(Number.isFinite(result.timings[phase]) && result.timings[phase] >= 0);
  }
  assert.equal(result.timings.totalMs,
    result.timings.prepareMs + result.timings.executeMs + result.timings.decodeMs);
  assert.throws(() => instance.render({ format: { kind: "bogus" }, width: 80 }),
    /unknown Format kind/);
  console.log("timing and malformed-input contract: PASS");
}

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = fileURLToPath(new URL(".", import.meta.url));
const [binaryenArg, outputArg] = process.argv.slice(2);
assert(binaryenArg !== undefined && outputArg !== undefined,
  "usage: node check.mjs BINARYEN_BIN OUTPUT_DIR");
const binaryen = resolve(binaryenArg);
const output = resolve(outputArg);
mkdirSync(output, { recursive: true });

const features = [
  "--enable-nontrapping-float-to-int",
  "--enable-multivalue",
];
const optimize = [
  ...features,
  "-O3",
  "--closed-world",
  "--remove-unused-module-elements",
  "--vacuum",
];
const originRows = [
  ...Array.from({ length: 7 }, (_, index) =>
    `fir-wasm-origin/1/fixture.entry:${index + 1}`),
  "fir-wasm-origin/2/fixture.frontierDead:1",
  ...Array.from({ length: 3 }, (_, index) =>
    `fir-wasm-origin/0/runtime.helper:${index + 1}`),
  "fir-wasm-origin/1/runtime.dead:1",
];
const sourceOrigins = new Set(originRows);

function run(tool, args, { quiet = false } = {}) {
  return execFileSync(join(binaryen, tool), args, {
    encoding: "utf8",
    stdio: quiet ? ["ignore", "ignore", "inherit"] :
      ["ignore", "pipe", "inherit"],
  });
}

const binaryenVersion = run("wasm-opt", ["--version"]).trim();
assert.equal(binaryenVersion,
  "wasm-opt version 128 (version_127-18-g2eb472cd6)");

function equalFile(left, right, message) {
  assert.deepEqual(readFileSync(left), readFileSync(right), message);
}

function sha256(path) {
  return createHash("sha256").update(readFileSync(path)).digest("hex");
}

const base64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
function decodeVlq(text, start) {
  let value = 0;
  let shift = 0;
  let index = start;
  while (index < text.length) {
    const digit = base64.indexOf(text[index]);
    assert.notEqual(digit, -1, `invalid source-map VLQ at ${index}`);
    index += 1;
    value |= (digit & 31) << shift;
    if ((digit & 32) === 0) {
      const negative = (value & 1) === 1;
      const magnitude = value >>> 1;
      return { value: negative ? -magnitude : magnitude, index };
    }
    shift += 5;
  }
  throw new Error("unterminated source-map VLQ");
}

function sourceLocations(sourceMapPath) {
  const sourceMap = JSON.parse(readFileSync(sourceMapPath, "utf8"));
  assert.equal(sourceMap.version, 3);
  let sourceIndex = 0;
  let sourceLine = 0;
  let sourceColumn = 0;
  const locations = [];
  for (const generatedLine of sourceMap.mappings.split(";")) {
    let generatedColumn = 0;
    for (const segment of generatedLine.split(",")) {
      if (segment === "") continue;
      const fields = [];
      let index = 0;
      while (index < segment.length) {
        const decoded = decodeVlq(segment, index);
        fields.push(decoded.value);
        index = decoded.index;
      }
      assert(fields.length === 1 || fields.length === 4 || fields.length === 5,
        `unsupported source-map segment ${segment}`);
      generatedColumn += fields[0];
      if (fields.length >= 4) {
        sourceIndex += fields[1];
        sourceLine += fields[2];
        sourceColumn += fields[3];
        assert(sourceIndex >= 0 && sourceIndex < sourceMap.sources.length);
        assert(sourceLine >= 0 && sourceColumn >= 0 && generatedColumn >= 0);
        locations.push({
          generatedColumn,
          source: sourceMap.sources[sourceIndex],
          line: sourceLine + 1,
        });
      }
    }
  }
  return locations;
}

function classify(mapPath) {
  const locations = sourceLocations(mapPath);
  const mappedKeys = new Set(locations.map(({ source, line }) =>
    `${source}:${line}`));
  const unknown = [...mappedKeys].filter(key => !sourceOrigins.has(key));
  const deleted = [...sourceOrigins].filter(key => !mappedKeys.has(key));
  const duplicateKeys = [...mappedKeys].filter(key =>
    locations.filter(({ source, line }) => `${source}:${line}` === key).length > 1);
  const ambiguous = [...sourceOrigins].filter(key =>
    originRows.filter(candidate => candidate === key).length > 1);

  assert.equal(unknown.length, 0, "optimizer produced an unattributed location");
  assert.equal(ambiguous.length, 0, "origin table contains a duplicate location key");
  assert(mappedKeys.has("fir-wasm-origin/0/runtime.helper:3"),
    "inlined helper add lost its origin");
  assert(mappedKeys.has("fir-wasm-origin/1/fixture.entry:6"),
    "frontier add lost its origin");
  assert(!mappedKeys.has("fir-wasm-origin/1/fixture.entry:3"),
    "eliminated call site unexpectedly survived");
  assert(deleted.includes("fir-wasm-origin/2/fixture.frontierDead:1"));
  assert(deleted.includes("fir-wasm-origin/1/runtime.dead:1"));

  return {
    schema: "fir.wasm.instruction-provenance-fixture/v1",
    mapped: [...mappedKeys].sort(),
    deleted: deleted.sort(),
    unknown,
    ambiguous,
    // Multiple output expressions may legitimately carry one origin after
    // propagation. This diagnostic list makes that multiplicity explicit; it
    // is not resolved by ordering or nearest-neighbor matching.
    repeatedMappings: duplicateKeys.sort(),
    mappingCount: locations.length,
  };
}

function pipeline(label) {
  const path = name => join(output, `${label}-${name}`);
  const frontierMap = path("frontier.map");
  const runtimeMap = path("runtime.map");
  const frontier = path("frontier.wasm");
  const runtime = path("runtime.wasm");

  run("wasm-as", [...features, "--debuginfo", "--source-map", frontierMap,
    join(here, "frontier.wat"), "-o", frontier]);
  run("wasm-as", [...features, "--debuginfo", "--source-map", runtimeMap,
    join(here, "runtime.wat"), "-o", runtime]);

  const mergedRelease = path("merged-release.wasm");
  run("wasm-merge", [...features, frontier, "env", runtime, "lean.extern",
    "-o", mergedRelease]);
  const mergedModule = new WebAssembly.Module(readFileSync(mergedRelease));
  assert.deepEqual(WebAssembly.Module.imports(mergedModule), []);
  const mergedExports = WebAssembly.Module.exports(mergedModule);
  const graph = path("exports.json");
  writeFileSync(graph, `${JSON.stringify(mergedExports.map((entry, index) => ({
    name: `fixture$export$${index}`,
    export: entry.name,
    ...(entry.name === "fixture.entry" ? { root: true } : {}),
  })))}\n`);

  const privateRelease = path("private-release.wasm");
  run("wasm-metadce", [...features, mergedRelease, "--quiet",
    `--graph-file=${graph}`, "-o", privateRelease], { quiet: true });
  const reorderedRelease = path("reordered-release.wasm");
  run("wasm-opt", [...features, "--reorder-functions", privateRelease,
    "-o", reorderedRelease]);
  const release = path("release.wasm");
  run("wasm-opt", [...optimize, "--strip-debug", "--strip-dwarf",
    reorderedRelease, "-o", release]);

  const mergedMap = path("merged.map");
  const merged = path("merged.wasm");
  run("wasm-merge", [...features, "--debuginfo",
    frontier, "env", "--input-source-map", frontierMap,
    runtime, "lean.extern", "--input-source-map", runtimeMap,
    "--output-source-map", mergedMap, "-o", merged]);
  const privateMap = path("private.map");
  const privateWasm = path("private.wasm");
  run("wasm-metadce", [...features, "--debuginfo",
    "--input-source-map", mergedMap, "--output-source-map", privateMap,
    merged, "--quiet", `--graph-file=${graph}`, "-o", privateWasm],
  { quiet: true });
  const reorderedMap = path("reordered.map");
  const reordered = path("reordered.wasm");
  run("wasm-opt", [...features, "--debuginfo",
    "--input-source-map", privateMap, "--output-source-map", reorderedMap,
    "--reorder-functions", privateWasm, "-o", reordered]);
  const finalMap = path("final.map");
  const companion = path("companion.wasm");
  run("wasm-opt", [...optimize, "--debuginfo", "--propagate-debug-locs",
    "--input-source-map", reorderedMap, "--output-source-map", finalMap,
    "--output-source-map-url=instruction-provenance.map", reordered,
    "-o", companion]);
  const stripped = path("companion-stripped.wasm");
  run("wasm-opt", ["--strip-debug", "--strip-dwarf", companion,
    "-o", stripped]);
  equalFile(release, stripped,
    "stripped provenance companion changed canonical release bytes");

  const finalModule = new WebAssembly.Module(readFileSync(release));
  assert.deepEqual(WebAssembly.Module.imports(finalModule), []);
  assert.deepEqual(WebAssembly.Module.exports(finalModule), [
    { name: "fixture.entry", kind: "function" },
  ]);
  const classification = classify(finalMap);
  const report = path("report.json");
  writeFileSync(report, `${JSON.stringify({
    ...classification,
    binaryenVersion,
    release: { bytes: readFileSync(release).length, sha256: sha256(release) },
    companion: {
      bytes: readFileSync(companion).length,
      sha256: sha256(companion),
    },
    sourceMap: {
      bytes: readFileSync(finalMap).length,
      sha256: sha256(finalMap),
    },
  }, null, 2)}\n`);
  return { release, companion, finalMap, report, classification };
}

const first = pipeline("first");
const second = pipeline("second");
equalFile(first.release, second.release, "release fixture is nondeterministic");
equalFile(first.companion, second.companion,
  "provenance companion is nondeterministic");
equalFile(first.finalMap, second.finalMap, "source map is nondeterministic");
equalFile(first.report, second.report, "classification report is nondeterministic");

console.log(`instruction provenance fixture: ${first.classification.mapped.length} mapped, ` +
  `${first.classification.deleted.length} deleted, ` +
  `${first.classification.unknown.length} unknown, ` +
  `${first.classification.ambiguous.length} ambiguous`);

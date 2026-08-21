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
const profilingGapSource = "fir-wasm-unmapped/profiling-v1";

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

function encodeVlq(value) {
  let remaining = Math.abs(value) * 2 + (value < 0 ? 1 : 0);
  let encoded = "";
  do {
    let digit = remaining % 32;
    remaining = Math.floor(remaining / 32);
    if (remaining !== 0) digit |= 32;
    encoded += base64[digit];
  } while (remaining !== 0);
  return encoded;
}

function decodeMappings(sourceMap) {
  let sourceIndex = 0;
  let sourceLine = 0;
  let sourceColumn = 0;
  let nameIndex = 0;
  return sourceMap.mappings.split(";").map(generatedLine => {
    let generatedColumn = 0;
    const segments = [];
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
      const decoded = { generatedColumn };
      if (fields.length >= 4) {
        sourceIndex += fields[1];
        sourceLine += fields[2];
        sourceColumn += fields[3];
        assert(sourceIndex >= 0 && sourceIndex < sourceMap.sources.length);
        assert(sourceLine >= 0 && sourceColumn >= 0 && generatedColumn >= 0);
        Object.assign(decoded, { sourceIndex, sourceLine, sourceColumn });
        if (fields.length === 5) {
          nameIndex += fields[4];
          assert(nameIndex >= 0 && nameIndex < sourceMap.names.length);
          decoded.nameIndex = nameIndex;
        }
      }
      segments.push(decoded);
    }
    return segments;
  });
}

function encodeMappings(lines) {
  let sourceIndex = 0;
  let sourceLine = 0;
  let sourceColumn = 0;
  let nameIndex = 0;
  return lines.map(segments => {
    let generatedColumn = 0;
    return segments.map(segment => {
      const fields = [segment.generatedColumn - generatedColumn];
      generatedColumn = segment.generatedColumn;
      if (segment.sourceIndex !== undefined) {
        fields.push(segment.sourceIndex - sourceIndex);
        fields.push(segment.sourceLine - sourceLine);
        fields.push(segment.sourceColumn - sourceColumn);
        sourceIndex = segment.sourceIndex;
        sourceLine = segment.sourceLine;
        sourceColumn = segment.sourceColumn;
        if (segment.nameIndex !== undefined) {
          fields.push(segment.nameIndex - nameIndex);
          nameIndex = segment.nameIndex;
        }
      }
      return fields.map(encodeVlq).join("");
    }).join(",");
  }).join(";");
}

function sourceLocations(sourceMapPath) {
  const sourceMap = JSON.parse(readFileSync(sourceMapPath, "utf8"));
  assert.equal(sourceMap.version, 3);
  return decodeMappings(sourceMap).flatMap(segments =>
    segments.filter(segment => segment.sourceIndex !== undefined).map(segment => ({
      generatedColumn: segment.generatedColumn,
      source: sourceMap.sources[segment.sourceIndex],
      line: segment.sourceLine + 1,
    })));
}

function writeProfilingProjection(exactMapPath, projectionPath) {
  const exact = JSON.parse(readFileSync(exactMapPath, "utf8"));
  assert.equal(exact.version, 3);
  assert(!exact.sources.includes(profilingGapSource),
    "exact map already contains the reserved profiling-gap source");
  const exactLines = decodeMappings(exact);
  const gapSourceIndex = exact.sources.length;
  let gapLine = 0;
  const projectedLines = exactLines.map(segments => segments.map(segment => {
    if (segment.sourceIndex !== undefined) return { ...segment };
    return {
      generatedColumn: segment.generatedColumn,
      sourceIndex: gapSourceIndex,
      sourceLine: gapLine++,
      sourceColumn: 0,
    };
  }));
  assert(gapLine > 0, "fixture no longer exercises an unmapped interval");
  const projection = {
    ...exact,
    sources: [...exact.sources, profilingGapSource],
    mappings: encodeMappings(projectedLines),
  };
  if (exact.sourcesContent !== undefined) {
    projection.sourcesContent = [...exact.sourcesContent, null];
  }
  const roundTrip = decodeMappings(projection);
  assert.equal(roundTrip.flat().length, exactLines.flat().length);
  assert(roundTrip.flat().every(segment => segment.sourceIndex !== undefined),
    "profiling projection still contains a V8-incompatible unmapped segment");
  let expectedGapLine = 0;
  for (const [lineIndex, exactSegments] of exactLines.entries()) {
    const projectedSegments = roundTrip[lineIndex];
    assert.equal(projectedSegments.length, exactSegments.length);
    for (const [segmentIndex, exactSegment] of exactSegments.entries()) {
      const projectedSegment = projectedSegments[segmentIndex];
      assert.equal(projectedSegment.generatedColumn, exactSegment.generatedColumn);
      if (exactSegment.sourceIndex !== undefined) {
        assert.deepEqual(projectedSegment, exactSegment,
          "profiling projection changed an authoritative mapped segment");
      } else {
        assert.deepEqual(projectedSegment, {
          generatedColumn: exactSegment.generatedColumn,
          sourceIndex: gapSourceIndex,
          sourceLine: expectedGapLine++,
          sourceColumn: 0,
        }, "profiling projection failed to preserve an explicit gap identity");
      }
    }
  }
  assert.equal(expectedGapLine, gapLine);
  writeFileSync(projectionPath, `${JSON.stringify(projection)}\n`);
  return { gapCount: gapLine };
}

function classify(mapPath, { expectedUnknown = [] } = {}) {
  const locations = sourceLocations(mapPath);
  const mappedKeys = new Set(locations.map(({ source, line }) =>
    `${source}:${line}`));
  const unknown = [...mappedKeys].filter(key => !sourceOrigins.has(key));
  const deleted = [...sourceOrigins].filter(key => !mappedKeys.has(key));
  const duplicateKeys = [...mappedKeys].filter(key =>
    locations.filter(({ source, line }) => `${source}:${line}` === key).length > 1);
  const ambiguous = [...sourceOrigins].filter(key =>
    originRows.filter(candidate => candidate === key).length > 1);

  assert.deepEqual(unknown.sort(), [...expectedUnknown].sort(),
    "map produced an unexpected unattributed location");
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
  const profilingMap = path("profiling.map");
  const projection = writeProfilingProjection(finalMap, profilingMap);
  const expectedProfilingUnknown = Array.from({ length: projection.gapCount },
    (_, index) => `${profilingGapSource}:${index + 1}`);
  const profilingClassification = classify(profilingMap, {
    expectedUnknown: expectedProfilingUnknown,
  });
  assert.deepEqual(profilingClassification.mapped,
    [...classification.mapped, ...expectedProfilingUnknown].sort());
  assert.deepEqual(profilingClassification.deleted, classification.deleted);
  assert.deepEqual(profilingClassification.ambiguous, classification.ambiguous);
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
    profilingProjection: {
      schema: "fir.wasm.instruction-profiling-map/v1",
      gapSource: profilingGapSource,
      explicitUnknown: profilingClassification.unknown,
      bytes: readFileSync(profilingMap).length,
      sha256: sha256(profilingMap),
    },
  }, null, 2)}\n`);
  return {
    release,
    companion,
    finalMap,
    profilingMap,
    report,
    classification,
    profilingClassification,
  };
}

const first = pipeline("first");
const second = pipeline("second");
equalFile(first.release, second.release, "release fixture is nondeterministic");
equalFile(first.companion, second.companion,
  "provenance companion is nondeterministic");
equalFile(first.finalMap, second.finalMap, "source map is nondeterministic");
equalFile(first.profilingMap, second.profilingMap,
  "profiling projection is nondeterministic");
equalFile(first.report, second.report, "classification report is nondeterministic");

console.log(`instruction provenance fixture: ${first.classification.mapped.length} mapped, ` +
  `${first.classification.deleted.length} deleted, ` +
  `${first.classification.unknown.length} unknown, ` +
  `${first.classification.ambiguous.length} ambiguous, ` +
  `${first.profilingClassification.unknown.length} explicit profiling gap`);

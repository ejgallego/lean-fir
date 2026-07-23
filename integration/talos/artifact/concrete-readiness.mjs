import assert from "node:assert/strict";
import { readFile, readdir, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

import { concreteArtifactExternalRegistry } from "./concrete-artifact-external-registry.mjs";
import {
  CONCRETE_FIXTURES,
  CONCRETE_SOURCE_PROBES,
  DEFAULT_EXTERNAL_FAULTS,
  EXPECTED_CONCRETE_FAULTS,
  REJECTED_FRAGMENT_FIXTURES,
} from "./concrete-corpus.mjs";
import { ConcreteHost } from "./concrete-host.mjs";

const OPERATION_RUNTIME_OP = Object.freeze({
  naturalLiteral: "literal",
  stringLiteral: "literal",
  allocCtor: "allocCtor",
  objectProj: "objectProj",
  usizeProj: "usizeProj",
  scalarProj: "scalarProj",
  cacheSet: "cacheSet",
  partialApply: "partialApply",
  closureMatches: "closureMatches",
  closureProj: "closureProj",
  reset: "reset",
  reuse: "reuse",
  box: "box",
  unbox: "unbox",
  isShared: "isShared",
  objectSet: "objectSet",
  usizeSet: "usizeSet",
  scalarSet: "scalarSet",
  setTag: "setTag",
  inc: "inc",
  dec: "dec",
  delete: "delete",
  getTag: "getTag",
});

function canonicalValue(value) {
  if (Array.isArray(value)) {
    return value.map(canonicalValue);
  }
  if (value && typeof value === "object") {
    return Object.fromEntries(Object.keys(value).sort().map((key) =>
      [key, canonicalValue(value[key])]));
  }
  return value;
}

function sortedUnique(values) {
  return [...new Set(values)].sort();
}

function checkedNameSet(values, context) {
  assert.ok(Array.isArray(values), `${context} must be an array`);
  assert.equal(new Set(values).size, values.length, `${context} contains duplicates`);
  for (const value of values) {
    assert.ok(typeof value === "string" && value.length > 0,
      `${context} contains a malformed name`);
  }
  return new Set(values);
}

function parseCoverageMatrix(text) {
  const rows = new Map();
  for (const line of text.split("\n")) {
    if (!line.startsWith("| `")) continue;
    const cells = line.split("|").slice(1, -1).map((cell) => cell.trim());
    assert.equal(cells.length, 5, `malformed W6 coverage row: ${line}`);
    const match = /^`([^`]+)`$/.exec(cells[0]);
    assert.ok(match, `malformed W6 RuntimeOp cell: ${cells[0]}`);
    const runtimeOp = match[1];
    assert.ok(!rows.has(runtimeOp), `duplicate W6 coverage row: ${runtimeOp}`);
    const detail = {
      runtimeOp,
      concreteExecutable: cells[1],
      successfulRefinement: cells[2],
      structuredFailures: cells[3],
      compositionArtifact: cells[4],
    };
    const statusText = cells.slice(1).join(" ").toLowerCase();
    detail.proofStatus = /\b(partial|pending|blocked)\b/.test(statusText)
      ? "partial"
      : "complete";
    detail.bugCards = sortedUnique(
      cells.slice(1).join(" ").match(/FIR-BUG-[a-z0-9-]+/g) ?? [],
    );
    rows.set(runtimeOp, detail);
  }
  assert.ok(rows.size > 0, "W6 coverage matrix contains no RuntimeOp rows");
  return rows;
}

function fixtureClassifications() {
  const successes = checkedNameSet(CONCRETE_FIXTURES, "concrete success fixtures");
  const rejected = checkedNameSet(
    REJECTED_FRAGMENT_FIXTURES, "concrete rejected-fragment fixtures");
  const expectedFaults = checkedNameSet(
    EXPECTED_CONCRETE_FAULTS.map(([fixture]) => fixture),
    "concrete expected-fault fixtures",
  );
  const all = new Map();
  for (const [status, fixtures] of [
    ["success", successes],
    ["rejected-fragment", rejected],
    ["expected-fault", expectedFaults],
  ]) {
    for (const fixture of fixtures) {
      assert.ok(!all.has(fixture), `concrete fixture ${fixture} has multiple classifications`);
      all.set(fixture, status);
    }
  }
  for (const [fixture] of DEFAULT_EXTERNAL_FAULTS) {
    assert.ok(successes.has(fixture),
      `default external fault fixture ${fixture} must also be a success fixture`);
  }
  return all;
}

async function readManifest(path, id, requireFixture) {
  const manifest = JSON.parse(await readFile(path, "utf8"));
  assert.ok(manifest && typeof manifest === "object" && !Array.isArray(manifest),
    `${id} manifest must be an object`);
  assert.ok(Array.isArray(manifest.imports), `${id} manifest imports must be an array`);
  if (requireFixture) {
    assert.equal(manifest.fixture, id, `${id} manifest fixture mismatch`);
  }
  for (const [index, descriptor] of manifest.imports.entries()) {
    assert.ok(descriptor && typeof descriptor === "object" && !Array.isArray(descriptor),
      `${id} import ${index} must be an object`);
    assert.ok(typeof descriptor.module === "string" && descriptor.module.length > 0,
      `${id} import ${index} has a malformed module`);
    assert.ok(typeof descriptor.name === "string" && descriptor.name.length > 0,
      `${id} import ${index} has a malformed name`);
    assert.ok(descriptor.operation && typeof descriptor.operation === "object" &&
      typeof descriptor.operation.kind === "string",
      `${id} import ${index} has a malformed operation`);
    if (descriptor.operation.kind === "external") {
      assert.ok(typeof descriptor.operation.declaration === "string" &&
        descriptor.operation.declaration.length > 0,
        `${id} import ${index} has a malformed external declaration`);
    }
  }
  return manifest;
}

function preflightManifest(manifest) {
  const blockers = [];
  try {
    const host = new ConcreteHost(manifest.imports);
    host.imports(manifest.imports);
  } catch (error) {
    blockers.push({ kind: "import-construction", message: String(error.message ?? error) });
  }
  if (manifest.initialRuntime !== undefined) {
    try {
      new ConcreteHost(manifest.imports, manifest.initialRuntime);
    } catch (error) {
      blockers.push({ kind: "initial-runtime", message: String(error.message ?? error) });
    }
  }
  const missingExternals = sortedUnique(manifest.imports
    .filter((descriptor) => descriptor.operation.kind === "external")
    .map((descriptor) => descriptor.operation.declaration)
    .filter((declaration) => !Object.hasOwn(concreteArtifactExternalRegistry, declaration)));
  if (missingExternals.length > 0) {
    blockers.push({ kind: "external-implementations", declarations: missingExternals });
  }
  return blockers;
}

function registerImports(inventory, scope, id, imports) {
  for (const descriptor of imports) {
    const operation = canonicalValue(descriptor.operation);
    const operationKind = operation.kind;
    assert.ok(operationKind === "external" ||
      Object.hasOwn(OPERATION_RUNTIME_OP, operationKind),
    `unmapped concrete operation kind: ${operationKind}`);
    const key = JSON.stringify([scope, id, descriptor.module, descriptor.name]);
    assert.ok(!inventory.has(key),
      `${id} has duplicate import identity ${descriptor.module}.${descriptor.name}`);
    inventory.set(key, {
      module: descriptor.module,
      name: descriptor.name,
      operation,
      artifactFixtures: new Set(),
      sourceProbes: new Set(),
      count: 0,
    });
    const entry = inventory.get(key);
    entry.count += 1;
    entry[scope].add(id);
  }
}

function coverageForOperation(operationKind, coverageRows) {
  if (operationKind === "external") {
    return {
      domain: "external",
      source: "integration/talos/W6-COVERAGE.md#cross-cutting-w65-state",
      proofStatus: "cross-cutting",
      bugCards: [],
    };
  }
  const runtimeOp = OPERATION_RUNTIME_OP[operationKind];
  const coverage = coverageRows.get(runtimeOp);
  assert.ok(coverage, `missing W6 coverage row for RuntimeOp.${runtimeOp}`);
  return { domain: "runtime", ...coverage };
}

export async function buildConcreteReadinessReport(
  artifactDirectory,
  sourceDirectory,
  coveragePath,
) {
  const coverageRows = parseCoverageMatrix(await readFile(coveragePath, "utf8"));
  for (const runtimeOp of new Set(Object.values(OPERATION_RUNTIME_OP))) {
    assert.ok(coverageRows.has(runtimeOp),
      `W6 coverage matrix is missing mapped RuntimeOp.${runtimeOp}`);
  }

  const classifications = fixtureClassifications();
  const artifactFiles = (await readdir(artifactDirectory))
    .filter((name) => name.endsWith(".wasm.json"))
    .sort();
  const artifactIds = artifactFiles.map((name) => name.slice(0, -".wasm.json".length));
  assert.deepStrictEqual(artifactIds, [...classifications.keys()].sort(),
    "emitted artifact inventory disagrees with concrete fixture classifications");

  const importInventory = new Map();
  const artifactFixtures = [];
  for (const id of artifactIds) {
    const manifest = await readManifest(
      join(artifactDirectory, `${id}.wasm.json`), id, true);
    const blockers = preflightManifest(manifest);
    registerImports(importInventory, "artifactFixtures", id, manifest.imports);
    artifactFixtures.push({
      id,
      status: classifications.get(id),
      ready: blockers.length === 0 && classifications.get(id) !== "rejected-fragment",
      importCount: manifest.imports.length,
      operationKinds: sortedUnique(manifest.imports.map((item) => item.operation.kind)),
      blockers,
    });
  }

  checkedNameSet(CONCRETE_SOURCE_PROBES, "concrete source probes");
  const sourceProbes = [];
  for (const id of [...CONCRETE_SOURCE_PROBES].sort()) {
    const manifest = await readManifest(
      join(sourceDirectory, `${id}.wasm.json`), id, false);
    const blockers = preflightManifest(manifest);
    registerImports(importInventory, "sourceProbes", id, manifest.imports);
    sourceProbes.push({
      id,
      ready: blockers.length === 0,
      importCount: manifest.imports.length,
      operationKinds: sortedUnique(manifest.imports.map((item) => item.operation.kind)),
      blockers,
    });
  }

  const imports = [...importInventory.values()]
    .sort((left, right) =>
      left.module.localeCompare(right.module) || left.name.localeCompare(right.name))
    .map((entry) => ({
      module: entry.module,
      name: entry.name,
      operation: entry.operation,
      coverage: coverageForOperation(entry.operation.kind, coverageRows),
      count: entry.count,
      artifactFixtures: [...entry.artifactFixtures].sort(),
      sourceProbes: [...entry.sourceProbes].sort(),
    }));

  const operationKinds = sortedUnique(imports.map((entry) => entry.operation.kind));
  const operations = operationKinds.map((operationKind) => {
    const matching = imports.filter((entry) => entry.operation.kind === operationKind);
    return {
      operationKind,
      coverage: coverageForOperation(operationKind, coverageRows),
      importIdentities: matching.length,
      importInstances: matching.reduce((total, entry) => total + entry.count, 0),
      artifactFixtures: sortedUnique(matching.flatMap((entry) => entry.artifactFixtures)),
      sourceProbes: sortedUnique(matching.flatMap((entry) => entry.sourceProbes)),
    };
  });

  const readyArtifacts = artifactFixtures.filter((fixture) => fixture.ready);
  const readySources = sourceProbes.filter((probe) => probe.ready);
  const artifactSwitchReady = readyArtifacts.length === artifactFixtures.length;
  const sourceProbeSwitchReady = readySources.length === sourceProbes.length;
  const proofCoverageComplete = operations.every((operation) =>
    operation.coverage.proofStatus === "complete");
  return canonicalValue({
    version: 1,
    scope: "fir-wasm-generated-artifacts",
    coverageSource: "integration/talos/W6-COVERAGE.md",
    summary: {
      artifactFixtures: artifactFixtures.length,
      artifactSuccessFixtures: artifactFixtures.filter((item) => item.status === "success").length,
      artifactExpectedFaultFixtures:
        artifactFixtures.filter((item) => item.status === "expected-fault").length,
      artifactRejectedFixtures:
        artifactFixtures.filter((item) => item.status === "rejected-fragment").length,
      readyArtifactFixtures: readyArtifacts.length,
      sourceProbes: sourceProbes.length,
      readySourceProbes: readySources.length,
      blockedSourceProbes: sourceProbes.length - readySources.length,
      importIdentities: imports.length,
      importInstances: imports.reduce((total, entry) => total + entry.count, 0),
      operationFamilies: operations.length,
      artifactSwitchReady,
      sourceProbeSwitchReady,
      proofCoverageComplete,
    },
    artifactFixtures,
    sourceProbes,
    operations,
    imports,
    notClaimed: [
      "proof completeness while W6 coverage rows remain partial or pending",
      "concrete execution of a source probe classified as preflight-ready",
      "concrete execution of the shared validation product bundle",
    ],
  });
}

async function main(args) {
  const requireArtifactReady = args.includes("--require-artifact-ready");
  const positional = args.filter((arg) => !arg.startsWith("--"));
  if (positional.length !== 4) {
    throw new Error(
      "usage: node concrete-readiness.mjs " +
      "ARTIFACT_DIR SOURCE_DIR W6_COVERAGE_MD OUTPUT_JSON [--require-artifact-ready]",
    );
  }
  const [artifactDirectory, sourceDirectory, coveragePath, outputPath] = positional;
  const report = await buildConcreteReadinessReport(
    artifactDirectory, sourceDirectory, coveragePath);
  await writeFile(outputPath, `${JSON.stringify(report, null, 2)}\n`);
  console.log(
    `concrete readiness: artifacts ${report.summary.readyArtifactFixtures}/` +
    `${report.summary.artifactFixtures}, sources ${report.summary.readySourceProbes}/` +
    `${report.summary.sourceProbes}, imports ${report.summary.importIdentities}, ` +
    `operations ${report.summary.operationFamilies}`,
  );
  if (requireArtifactReady && !report.summary.artifactSwitchReady) {
    process.exitCode = 1;
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  await main(process.argv.slice(2));
}

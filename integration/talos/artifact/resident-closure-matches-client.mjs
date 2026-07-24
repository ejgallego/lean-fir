import { ConcreteHost } from "./concrete-host.mjs";

function expect(condition, message) {
  if (!condition) throw new Error(message);
}

function expectTrap(action, label) {
  try {
    action();
  } catch (error) {
    expect(error instanceof WebAssembly.RuntimeError,
      `${label} raised the wrong error type: ${error}`);
    return;
  }
  throw new Error(`${label} did not trap`);
}

function writeHeader(view, address, {
  kind = 2,
  flags = 2,
  refCount = 1,
  allocationBytes = 40,
  aux0 = 0,
  aux1 = 2,
  aux2 = 1,
  aux3 = 0,
} = {}) {
  view.setUint32(address + 0, kind, true);
  view.setUint32(address + 4, flags, true);
  view.setUint32(address + 8, refCount, true);
  view.setUint32(address + 12, allocationBytes, true);
  view.setUint32(address + 16, aux0, true);
  view.setUint32(address + 20, aux1, true);
  view.setUint32(address + 24, aux2, true);
  view.setUint32(address + 28, aux3, true);
}

function rawLayoutChecks(instance, memory, entries) {
  const view = new DataView(memory.buffer);
  entries.forEach((entry, index) => {
    const address = 1024 + index * 256;
    writeHeader(view, address, {
      aux0: entry.targetId,
      aux1: entry.arity,
      aux2: entry.fixed,
      allocationBytes: 32 + entry.fixed * 8,
    });
    expect(instance.exports[entry.entry](address) === 1,
      `${entry.entry} rejected its exact raw closure metadata`);
    entries.forEach((candidate) => {
      const expected = candidate.targetId === entry.targetId &&
        candidate.arity === entry.arity && candidate.fixed === entry.fixed ? 1 : 0;
      expect(instance.exports[candidate.entry](address) === expected,
        `${candidate.entry} returned the wrong raw match result`);
    });
  });

  const dead = 4096;
  writeHeader(view, dead, { flags: 0 });
  const wrongKind = 4352;
  writeHeader(view, wrongKind, { kind: 1 });
  const entry = instance.exports[entries[0].entry];
  expectTrap(() => entry(0), "resident closure match zero sentinel");
  expectTrap(() => entry(6), "resident closure match misaligned word");
  expectTrap(() => entry(17), "resident closure match immediate word");
  expectTrap(() => entry(dead), "resident closure match dead object");
  expectTrap(() => entry(wrongKind), "resident closure match non-closure object");
}

async function concreteHostChecks(module, entries, dispatch) {
  const operations = entries.map((entry) => ({
    kind: "partialApply",
    function: entry.function,
    arity: entry.arity,
    fixed: entry.fixed,
    fields: Array(entry.fixed).fill("tobject"),
    result: "tobject",
  }));
  const host = new ConcreteHost(
    operations.map((operation) => ({ operation })),
    undefined,
    undefined,
    dispatch,
  );
  const instance = await WebAssembly.instantiate(module, {});
  host.attachMemory(instance.exports.memory);
  for (const [index, operation] of operations.entries()) {
    const args = operation.fields.map((_, field) =>
      host.encodeTagged(BigInt(10 + index + field)));
    const closure = host.partialApply(operation, args);
    for (const candidate of entries) {
      const expected = candidate.function === operation.function &&
        candidate.arity === operation.arity && candidate.fixed === operation.fixed ? 1 : 0;
      expect(instance.exports[candidate.entry](closure) === expected,
        `${candidate.entry} disagreed with the concrete closure header`);
    }
  }
}

export async function checkResidentClosureMatches({
  bytes,
  manifest,
}) {
  expect(Array.isArray(manifest.imports) && manifest.imports.length === 0,
    "resident closure-match module must have zero imports");
  expect(Array.isArray(manifest.entries) && manifest.entries.length === 4,
    "resident closure-match manifest must expose four discriminator cases");
  expect(Array.isArray(manifest.closureDispatch) &&
    manifest.closureDispatch.length === 2,
  "resident closure-match manifest must expose its stable dispatch table");
  expect(WebAssembly.validate(bytes),
    "resident closure-match bytes failed WebAssembly validation");
  const module = await WebAssembly.compile(bytes);
  expect(WebAssembly.Module.imports(module).length === 0,
    "resident closure-match binary must have zero imports");
  const instance = await WebAssembly.instantiate(module, {});
  expect(instance.exports.memory instanceof WebAssembly.Memory,
    "resident closure-match module must export its own memory");
  rawLayoutChecks(instance, instance.exports.memory, manifest.entries);
  await concreteHostChecks(module, manifest.entries, manifest.closureDispatch);
  return "PASS import-free Wasm-resident prettyM closure matches";
}

export async function checkFetchedResidentClosureMatches(artifactUrl) {
  const [moduleResponse, manifestResponse] = await Promise.all([
    fetch(artifactUrl),
    fetch(`${artifactUrl}.json`),
  ]);
  expect(moduleResponse.ok,
    `failed to fetch resident closure-match module: HTTP ${moduleResponse.status}`);
  expect(manifestResponse.ok,
    `failed to fetch resident closure-match manifest: HTTP ${manifestResponse.status}`);
  return checkResidentClosureMatches({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await manifestResponse.json(),
  });
}

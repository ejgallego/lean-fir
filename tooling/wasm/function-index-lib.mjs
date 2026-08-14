import assert from "node:assert/strict";
import { createHash } from "node:crypto";

const textDecoder = new TextDecoder("utf-8", { fatal: true });
const textEncoder = new TextEncoder();

export const sidecarSchema = "fir.wasm.function-index/v1";
export const captureSchema = "fir.wasm.function-capture/v1";

export function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function readU32(bytes, start) {
  let result = 0;
  let shift = 0;
  let offset = start;
  for (let index = 0; index < 5; index += 1) {
    assert(offset < bytes.length, "truncated unsigned LEB128 value");
    const byte = bytes[offset];
    offset += 1;
    result |= (byte & 0x7f) << shift;
    if ((byte & 0x80) === 0) {
      return { value: result >>> 0, offset };
    }
    shift += 7;
  }
  throw new Error("unsigned LEB128 value exceeds u32");
}

function encodeU32(value) {
  assert(Number.isSafeInteger(value) && value >= 0 && value <= 0xffffffff,
    `expected a u32, got ${value}`);
  const result = [];
  let remaining = value >>> 0;
  do {
    let byte = remaining & 0x7f;
    remaining >>>= 7;
    if (remaining !== 0) {
      byte |= 0x80;
    }
    result.push(byte);
  } while (remaining !== 0);
  return Buffer.from(result);
}

function readName(bytes, start) {
  const length = readU32(bytes, start);
  const end = length.offset + length.value;
  assert(end <= bytes.length, "truncated Wasm name");
  return {
    value: textDecoder.decode(bytes.subarray(length.offset, end)),
    offset: end,
  };
}

function encodeName(name) {
  const bytes = Buffer.from(textEncoder.encode(name));
  return Buffer.concat([encodeU32(bytes.length), bytes]);
}

function sections(bytes) {
  assert(bytes.length >= 8, "truncated Wasm header");
  assert.deepEqual([...bytes.subarray(0, 8)],
    [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00],
    "unsupported Wasm header");
  const result = [];
  let offset = 8;
  while (offset < bytes.length) {
    const start = offset;
    const id = bytes[offset];
    offset += 1;
    const size = readU32(bytes, offset);
    const payloadStart = size.offset;
    const end = payloadStart + size.value;
    assert(end <= bytes.length, `truncated Wasm section ${id}`);
    result.push({ id, start, payloadStart, end });
    offset = end;
  }
  return result;
}

function sectionById(bytes, id) {
  return sections(bytes).find((section) => section.id === id);
}

function vectorLength(bytes, section) {
  return section === undefined ? 0 : readU32(bytes, section.payloadStart).value;
}

function functionExports(bytes) {
  const section = sectionById(bytes, 7);
  if (section === undefined) {
    return [];
  }
  const count = readU32(bytes, section.payloadStart);
  const result = [];
  let offset = count.offset;
  for (let index = 0; index < count.value; index += 1) {
    const name = readName(bytes, offset);
    assert(name.offset < section.end, "truncated Wasm export descriptor");
    const kind = bytes[name.offset];
    const target = readU32(bytes, name.offset + 1);
    if (kind === 0) {
      result.push({ name: name.value, index: target.value });
    }
    offset = target.offset;
  }
  assert.equal(offset, section.end, "unexpected trailing export-section data");
  return result;
}

function functionBodyBytes(bytes) {
  const section = sectionById(bytes, 10);
  if (section === undefined) {
    return [];
  }
  const count = readU32(bytes, section.payloadStart);
  const result = [];
  let offset = count.offset;
  for (let index = 0; index < count.value; index += 1) {
    const body = readU32(bytes, offset);
    const end = body.offset + body.value;
    assert(end <= section.end, "truncated Wasm function body");
    result.push(body.value);
    offset = end;
  }
  assert.equal(offset, section.end, "unexpected trailing code-section data");
  return result;
}

export function moduleShape(bytes) {
  assert(WebAssembly.validate(bytes), "input is not a valid Wasm module");
  const module = new WebAssembly.Module(bytes);
  const functionImportCount = WebAssembly.Module.imports(module)
    .filter(({ kind }) => kind === "function").length;
  const definedFunctionCount = vectorLength(bytes, sectionById(bytes, 3));
  const bodies = functionBodyBytes(bytes);
  assert.equal(bodies.length, definedFunctionCount,
    "function and code sections disagree");
  return {
    byteLength: bytes.length,
    sha256: sha256(bytes),
    functionImportCount,
    definedFunctionCount,
    functionCount: functionImportCount + definedFunctionCount,
    functionExports: functionExports(bytes),
    functionBodyBytes: bodies,
  };
}

/** Binaryen's default name for a function in a stripped module. */
export function binaryenOptimizerName(index, functionImportCount) {
  assert(Number.isSafeInteger(index) && index >= 0,
    `invalid absolute Wasm function index ${index}`);
  assert(Number.isSafeInteger(functionImportCount) && functionImportCount >= 0,
    `invalid function import count ${functionImportCount}`);
  return index < functionImportCount ? `fimport$${index}` :
    String(index - functionImportCount);
}

/** Convert an absolute Wasm function index to Binaryen's defined ordinal. */
export function definedFunctionOrdinal(index, functionImportCount) {
  assert(Number.isSafeInteger(index) && index >= functionImportCount,
    `function ${index} is imported and has no local body`);
  return index - functionImportCount;
}

function isNameSection(bytes, section) {
  return section.id === 0 &&
    readName(bytes, section.payloadStart).value === "name";
}

function nameSection(identities) {
  const entries = identities.map(({ index, token }) =>
    Buffer.concat([encodeU32(index), encodeName(token)]));
  const functionNames = Buffer.concat([
    encodeU32(entries.length),
    ...entries,
  ]);
  const subsection = Buffer.concat([
    Buffer.from([1]),
    encodeU32(functionNames.length),
    functionNames,
  ]);
  const payload = Buffer.concat([encodeName("name"), subsection]);
  return Buffer.concat([
    Buffer.from([0]),
    encodeU32(payload.length),
    payload,
  ]);
}

export function injectFunctionIdentities(bytes, identities) {
  const shape = moduleShape(bytes);
  assert.equal(identities.length, shape.functionCount,
    "identity count must equal the module function count");
  assert.deepEqual(identities.map(({ index }) => index),
    Array.from({ length: shape.functionCount }, (_, index) => index),
    "function identities must be in contiguous index order");
  assert.equal(new Set(identities.map(({ token }) => token)).size,
    identities.length, "function identity tokens must be unique");
  const kept = sections(bytes).filter((section) => !isNameSection(bytes,
    section)).map((section) => bytes.subarray(section.start, section.end));
  return Buffer.concat([bytes.subarray(0, 8), ...kept,
    nameSection(identities)]);
}

function compilerShape(name) {
  if (name.includes("._closed_")) {
    return "closed-declaration";
  }
  if (name.includes(".spec_")) {
    return "specialization";
  }
  if (name.includes("._redArg")) {
    return "reduced-arity";
  }
  return "ordinary";
}

export function makeCapture(bytes, inventory, inputFile = null) {
  const shape = moduleShape(bytes);
  assert(Array.isArray(inventory.functions),
    "inventory.functions must be an array");
  assert.equal(inventory.functions.length, shape.definedFunctionCount,
    "inventory.functions must name every defined function in emitter order");
  const sourceFunctions = new Set(inventory.sourceFunctions ?? []);
  const residentHelpers = new Set(inventory.residentHelpers ?? []);
  const imports = WebAssembly.Module.imports(new WebAssembly.Module(bytes))
    .filter(({ kind }) => kind === "function");
  const identities = [];
  for (const [index, import_] of imports.entries()) {
    identities.push({
      index,
      token: String(index),
      name: `${import_.module}.${import_.name}`,
      origin: "function-import",
      compilerShape: "ordinary",
      import: { module: import_.module, name: import_.name },
    });
  }
  for (const [offset, name] of inventory.functions.entries()) {
    const index = shape.functionImportCount + offset;
    let origin = "unclassified-definition";
    if (sourceFunctions.has(name)) {
      origin = "lean-source";
    } else if (residentHelpers.has(name)) {
      origin = "resident-helper";
    }
    identities.push({
      index,
      token: String(index),
      name,
      origin,
      compilerShape: compilerShape(name),
    });
  }
  return {
    schemaVersion: captureSchema,
    inputArtifact: {
      ...(inputFile === null ? {} : { file: inputFile }),
      byteLength: shape.byteLength,
      sha256: shape.sha256,
      functionImportCount: shape.functionImportCount,
      definedFunctionCount: shape.definedFunctionCount,
    },
    identityProtocol: "binaryen-default-index-name/v1",
    identities,
  };
}

export function restampCapture(bytes, capture, functionMapSource,
  inputFile = null) {
  assert.equal(capture.schemaVersion, captureSchema,
    `unsupported capture schema ${capture.schemaVersion}`);
  const shape = moduleShape(bytes);
  const functionMap = parseFunctionMap(functionMapSource);
  assert.equal(functionMap.length, shape.functionCount,
    "stage function map and Wasm function count disagree");
  const previousIdentities = new Map(capture.identities.map((entry) =>
    [entry.token, entry]));
  const identities = functionMap.map(({ index, optimizerName }) => {
    const previous = previousIdentities.get(optimizerName);
    if (previous === undefined) {
      return {
        index,
        token: String(index),
        name: null,
        origin: "optimizer-or-linked-runtime",
        compilerShape: "unknown",
        upstreamOptimizerName: optimizerName,
      };
    }
    const { index: previousIndex, token: previousToken, ...identity } = previous;
    return {
      ...identity,
      index,
      token: String(index),
      upstreamIndex: previousIndex,
      upstreamOptimizerName: previousToken,
    };
  });
  return {
    schemaVersion: captureSchema,
    inputArtifact: {
      ...(inputFile === null ? {} : { file: inputFile }),
      byteLength: shape.byteLength,
      sha256: shape.sha256,
      functionImportCount: shape.functionImportCount,
      definedFunctionCount: shape.definedFunctionCount,
    },
    identityProtocol: "binaryen-default-index-name/v1",
    upstreamCapture: {
      inputArtifact: capture.inputArtifact,
      identityProtocol: capture.identityProtocol,
    },
    identities,
  };
}

export function parseFunctionMap(source) {
  const entries = [];
  for (const rawLine of source.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (line === "") {
      continue;
    }
    const match = /^(\d+):(.*)$/.exec(line);
    // Binaryen's import/export minifier emits rename diagnostics on the same
    // stream as --print-function-map. Only numeric map rows belong here.
    if (match === null) {
      continue;
    }
    assert.notEqual(match[2], "", `empty Binaryen function name at ${match[1]}`);
    entries.push({ index: Number(match[1]), optimizerName: match[2] });
  }
  entries.sort((left, right) => left.index - right.index);
  assert.deepEqual(entries.map(({ index }) => index),
    Array.from({ length: entries.length }, (_, index) => index),
    "Binaryen function map must contain every final index exactly once");
  assert.equal(new Set(entries.map(({ optimizerName }) => optimizerName)).size,
    entries.length, "Binaryen function names must be unique");
  return entries;
}

function dotName(source) {
  return JSON.parse(`"${source}"`);
}

export function parseCallGraph(source, functionMap) {
  const functionCount = functionMap.length;
  const calls = Array.from({ length: functionCount }, () => []);
  const unresolved = Array.from({ length: functionCount }, () => []);
  const indices = new Map(functionMap.map(({ index, optimizerName }) =>
    [optimizerName, index]));
  assert.equal(indices.size, functionCount,
    "call-graph function names must be unique");
  const edge = /^\s*"((?:[^"\\]|\\.)*)"\s*->\s*"((?:[^"\\]|\\.)*)"/;
  for (const line of source.split(/\r?\n/)) {
    const match = edge.exec(line);
    if (match === null) {
      continue;
    }
    const callerName = dotName(match[1]);
    const calleeName = dotName(match[2]);
    const caller = indices.get(callerName);
    if (caller === undefined) {
      continue;
    }
    const callee = indices.get(calleeName);
    if (callee !== undefined) {
      calls[caller].push(callee);
    } else {
      unresolved[caller].push(calleeName);
    }
  }
  return {
    calls: calls.map((items) => [...new Set(items)].sort((a, b) => a - b)),
    unresolved: unresolved.map((items) => [...new Set(items)].sort()),
  };
}

export function makeSidecar(bytes, capture, functionMapSource,
  callGraphSource, { artifactFile = null, producer = {} } = {}) {
  assert.equal(capture.schemaVersion, captureSchema,
    `unsupported capture schema ${capture.schemaVersion}`);
  const shape = moduleShape(bytes);
  const identityFunctionMap = parseFunctionMap(functionMapSource);
  assert.equal(identityFunctionMap.length, shape.functionCount,
    "Binaryen function map and final Wasm function count disagree");
  const graphFunctionMap = parseFunctionMap(callGraphSource);
  const finalFunctionMap = graphFunctionMap.length === 0 ?
    Array.from({ length: shape.functionCount }, (_, index) => ({
      index,
      optimizerName: binaryenOptimizerName(index, shape.functionImportCount),
    })) : graphFunctionMap;
  assert.equal(finalFunctionMap.length, shape.functionCount,
    "call-graph function map and final Wasm function count disagree");
  const graph = parseCallGraph(callGraphSource, finalFunctionMap);
  const identities = new Map(capture.identities.map((entry) =>
    [entry.token, entry]));
  const exportsByIndex = new Map();
  for (const { name, index } of shape.functionExports) {
    const names = exportsByIndex.get(index) ?? [];
    names.push(name);
    exportsByIndex.set(index, names);
  }
  const functions = identityFunctionMap.map(({ index,
    optimizerName: identityName }) => {
    const identity = identities.get(identityName);
    const optimizerName = finalFunctionMap[index].optimizerName;
    const imported = index < shape.functionImportCount;
    const bodyBytes = imported ? null :
      shape.functionBodyBytes[index - shape.functionImportCount];
    return {
      index,
      name: identity?.name ?? null,
      optimizerName,
      origin: identity?.origin ?? "optimizer-or-linked-runtime",
      compilerShape: identity?.compilerShape ?? "unknown",
      imported,
      bodyBytes,
      exportedAs: exportsByIndex.get(index) ?? [],
      directCallees: graph.calls[index],
      unresolvedCallTargets: graph.unresolved[index],
    };
  });
  const sidecar = {
    schemaVersion: sidecarSchema,
    artifact: {
      ...(artifactFile === null ? {} : { file: artifactFile }),
      byteLength: shape.byteLength,
      sha256: shape.sha256,
      functionImportCount: shape.functionImportCount,
      definedFunctionCount: shape.definedFunctionCount,
      functionCount: shape.functionCount,
    },
    capture: {
      schemaVersion: capture.schemaVersion,
      inputArtifact: capture.inputArtifact,
      identityProtocol: capture.identityProtocol,
      producer,
    },
    functions,
  };
  validateSidecar(bytes, sidecar);
  return sidecar;
}

export function validateSidecar(bytes, sidecar) {
  assert.equal(sidecar.schemaVersion, sidecarSchema,
    `unsupported sidecar schema ${sidecar.schemaVersion}`);
  const shape = moduleShape(bytes);
  assert.equal(sidecar.artifact.sha256, shape.sha256,
    "sidecar artifact SHA-256 does not match Wasm bytes");
  assert.equal(sidecar.artifact.byteLength, shape.byteLength,
    "sidecar artifact byte length does not match Wasm bytes");
  for (const key of ["functionImportCount", "definedFunctionCount",
    "functionCount"]) {
    assert.equal(sidecar.artifact[key], shape[key],
      `sidecar artifact ${key} does not match Wasm bytes`);
  }
  assert.equal(sidecar.functions.length, shape.functionCount,
    "sidecar must contain every final Wasm function");
  assert.deepEqual(sidecar.functions.map(({ index }) => index),
    Array.from({ length: shape.functionCount }, (_, index) => index),
    "sidecar functions must be in contiguous final-index order");
  const expectedExports = new Map(shape.functionExports.map(({ index,
    name }) => [name, index]));
  const actualExports = new Map();
  const optimizerNames = new Set();
  for (const function_ of sidecar.functions) {
    assert.equal(typeof function_.optimizerName, "string",
      `function ${function_.index} has no optimizer name`);
    assert(!optimizerNames.has(function_.optimizerName),
      `duplicate optimizer name ${function_.optimizerName}`);
    optimizerNames.add(function_.optimizerName);
    const imported = function_.index < shape.functionImportCount;
    assert.equal(function_.imported, imported,
      `function ${function_.index} import classification changed`);
    assert.equal(function_.bodyBytes, imported ? null :
      shape.functionBodyBytes[definedFunctionOrdinal(function_.index,
        shape.functionImportCount)],
    `function ${function_.index} body size does not match Wasm bytes`);
    if (imported) {
      assert.deepEqual(function_.directCallees, [],
        `imported function ${function_.index} cannot have callees`);
      assert.deepEqual(function_.unresolvedCallTargets, [],
        `imported function ${function_.index} cannot have unresolved callees`);
    }
    for (const name of function_.exportedAs) {
      assert(!actualExports.has(name), `duplicate sidecar export ${name}`);
      actualExports.set(name, function_.index);
    }
    for (const callee of function_.directCallees) {
      assert(Number.isSafeInteger(callee) && callee >= 0 &&
        callee < shape.functionCount,
      `invalid direct callee ${callee} for function ${function_.index}`);
    }
  }
  assert.deepEqual(actualExports, expectedExports,
    "sidecar function exports do not match Wasm exports");
  return sidecar;
}

export function inspectFunction(sidecar, selector) {
  let target;
  if (/^\d+$/.test(selector)) {
    target = sidecar.functions[Number(selector)];
  } else {
    const matches = sidecar.functions.filter(({ name, optimizerName,
      exportedAs }) => name === selector || optimizerName === selector ||
      exportedAs.includes(selector));
    assert(matches.length <= 1,
      `function selector is ambiguous: ${selector}`);
    target = matches[0];
  }
  assert(target !== undefined, `function not found: ${selector}`);
  const directCallers = sidecar.functions.filter(({ directCallees }) =>
    directCallees.includes(target.index)).map(({ index }) => index);
  return { ...target, directCallers };
}

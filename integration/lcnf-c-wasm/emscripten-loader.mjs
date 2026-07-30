const manifestSchemaVersion = 1;
const cIdentifier = /^[A-Za-z_][A-Za-z0-9_]*$/;
const artifactFilename = /^[A-Za-z0-9][A-Za-z0-9_.-]*$/;
const sha256Digest = /^[0-9a-f]{64}$/;

function fail(message) {
  throw new Error(`LCNF C/Wasm loader: ${message}`);
}

function defaultBaseURL() {
  if (typeof document !== "undefined" && document.baseURI !== undefined) {
    return new URL(document.baseURI);
  }
  return new URL(import.meta.url);
}

function asURL(value, baseURL = defaultBaseURL()) {
  return value instanceof URL ? value : new URL(value, baseURL);
}

async function readBytes(url) {
  if (url.protocol === "file:") {
    if (
      typeof process === "undefined" ||
      process.versions?.node === undefined
    ) {
      fail(`file URL is unavailable in this host: ${url}`);
    }
    const { readFile } = await import("node:fs/promises");
    return new Uint8Array(await readFile(url));
  }
  const response = await fetch(url);
  if (!response.ok) {
    fail(`could not fetch ${url}: HTTP ${response.status}`);
  }
  return new Uint8Array(await response.arrayBuffer());
}

async function hashBytes(bytes) {
  if (globalThis.crypto?.subtle !== undefined) {
    const digest = await globalThis.crypto.subtle.digest("SHA-256", bytes);
    return Array.from(new Uint8Array(digest), (byte) =>
      byte.toString(16).padStart(2, "0"),
    ).join("");
  }
  if (
    typeof process !== "undefined" &&
    process.versions?.node !== undefined
  ) {
    const { createHash } = await import("node:crypto");
    return createHash("sha256").update(bytes).digest("hex");
  }
  fail("host does not provide SHA-256");
}

function validateArtifact(label, artifact) {
  if (artifact === null || typeof artifact !== "object") {
    fail(`manifest ${label} artifact is missing`);
  }
  if (
    typeof artifact.file !== "string" ||
    !artifactFilename.test(artifact.file)
  ) {
    fail(`manifest ${label} filename is invalid`);
  }
  if (
    !Number.isSafeInteger(artifact.byteLength) ||
    artifact.byteLength <= 0
  ) {
    fail(`manifest ${label} byte length is invalid`);
  }
  if (
    typeof artifact.sha256 !== "string" ||
    !sha256Digest.test(artifact.sha256)
  ) {
    fail(`manifest ${label} digest is invalid`);
  }
}

function validateManifest(manifest) {
  if (manifest === null || typeof manifest !== "object") {
    fail("manifest must be an object");
  }
  if (manifest.schemaVersion !== manifestSchemaVersion) {
    fail(`unsupported manifest schema ${manifest.schemaVersion}`);
  }
  if (manifest.profile !== "emscripten") {
    fail(`unsupported manifest profile ${manifest.profile}`);
  }
  if (manifest.abi === null || typeof manifest.abi !== "object") {
    fail("manifest ABI is missing");
  }
  if (
    typeof manifest.abi.initialize !== "string" ||
    !cIdentifier.test(manifest.abi.initialize)
  ) {
    fail("manifest initializer export is invalid");
  }
  if (
    typeof manifest.abi.moduleInitializer !== "string" ||
    !cIdentifier.test(manifest.abi.moduleInitializer)
  ) {
    fail("manifest generated module initializer is invalid");
  }
  if (
    manifest.abi.start !== null &&
    (typeof manifest.abi.start !== "string" ||
      !cIdentifier.test(manifest.abi.start))
  ) {
    fail("manifest start action is invalid");
  }
  if (!Array.isArray(manifest.abi.exports)) {
    fail("manifest exports must be an array");
  }
  const uniqueExports = new Set();
  for (const symbol of manifest.abi.exports) {
    if (typeof symbol !== "string" || !cIdentifier.test(symbol)) {
      fail(`manifest export is invalid: ${symbol}`);
    }
    if (uniqueExports.has(symbol)) {
      fail(`manifest export is duplicated: ${symbol}`);
    }
    uniqueExports.add(symbol);
  }
  if (
    manifest.artifacts === null ||
    typeof manifest.artifacts !== "object"
  ) {
    fail("manifest artifacts are missing");
  }
  validateArtifact("module", manifest.artifacts.module);
  validateArtifact("Wasm", manifest.artifacts.wasm);
  if (manifest.runtime === null || typeof manifest.runtime !== "object") {
    fail("manifest runtime requirements are missing");
  }
  if (typeof manifest.runtime.threads !== "boolean") {
    fail("manifest thread requirement is invalid");
  }
}

async function readManifest(source, configuredBaseURL) {
  if (
    source !== null &&
    typeof source === "object" &&
    !(source instanceof URL)
  ) {
    if (configuredBaseURL === undefined) {
      fail("baseURL is required when loading a manifest object");
    }
    return {
      manifest: source,
      baseURL: asURL(configuredBaseURL),
    };
  }

  const manifestURL = asURL(source, configuredBaseURL);
  const bytes = await readBytes(manifestURL);
  let manifest;
  try {
    manifest = JSON.parse(new TextDecoder().decode(bytes));
  } catch (error) {
    fail(`could not parse manifest ${manifestURL}: ${error}`);
  }
  return {
    manifest,
    baseURL: new URL(".", manifestURL),
  };
}

async function verifyArtifact(label, artifact, url, suppliedBytes) {
  const bytes = suppliedBytes ?? (await readBytes(url));
  if (bytes.byteLength !== artifact.byteLength) {
    fail(
      `${label} byte length mismatch: expected ${artifact.byteLength}, got ${bytes.byteLength}`,
    );
  }
  const actualDigest = await hashBytes(bytes);
  if (actualDigest !== artifact.sha256) {
    fail(
      `${label} digest mismatch: expected ${artifact.sha256}, got ${actualDigest}`,
    );
  }
  return bytes;
}

export async function loadEmscriptenModule(
  manifestSource,
  {
    baseURL,
    moduleOptions = {},
    wasmBinary,
  } = {},
) {
  const { manifest, baseURL: artifactBaseURL } = await readManifest(
    manifestSource,
    baseURL,
  );
  validateManifest(manifest);
  if (
    manifest.runtime.threads &&
    typeof document !== "undefined" &&
    !globalThis.crossOriginIsolated
  ) {
    fail("threaded Wasm requires a cross-origin-isolated browser");
  }

  const moduleURL = new URL(manifest.artifacts.module.file, artifactBaseURL);
  const wasmURL = new URL(manifest.artifacts.wasm.file, artifactBaseURL);
  let suppliedWasm;
  if (wasmBinary !== undefined) {
    suppliedWasm = ArrayBuffer.isView(wasmBinary)
      ? new Uint8Array(
          wasmBinary.buffer,
          wasmBinary.byteOffset,
          wasmBinary.byteLength,
        )
      : new Uint8Array(wasmBinary);
  }
  const [moduleBytes, verifiedWasm] = await Promise.all([
    verifyArtifact(
      "JavaScript module",
      manifest.artifacts.module,
      moduleURL,
    ),
    verifyArtifact(
      "Wasm",
      manifest.artifacts.wasm,
      wasmURL,
      suppliedWasm,
    ),
  ]);
  void moduleBytes;

  const { default: createModule } = await import(moduleURL);
  if (typeof createModule !== "function") {
    fail(`JavaScript module has no default factory export: ${moduleURL}`);
  }
  const module = await createModule({
    ...moduleOptions,
    wasmBinary: verifiedWasm,
  });

  const initialize = module[`_${manifest.abi.initialize}`];
  if (typeof initialize !== "function") {
    fail(`module does not export ${manifest.abi.initialize}`);
  }
  const initializationCode = initialize();
  if (initializationCode !== 0) {
    fail(`module initialization failed with status ${initializationCode}`);
  }

  const exports = Object.create(null);
  for (const symbol of manifest.abi.exports) {
    const exported = module[`_${symbol}`];
    if (typeof exported !== "function") {
      fail(`module does not export ${symbol}`);
    }
    exports[symbol] = exported;
  }

  return {
    manifest,
    module,
    exports,
    wasmByteLength: verifiedWasm.byteLength,
  };
}

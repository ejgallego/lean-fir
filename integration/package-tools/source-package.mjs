import assert from "node:assert/strict";

export const SOURCE_PACKAGE_DESCRIPTOR_VERSION =
  "browser-benchmarks/source-package/v1";

function valueAt(root, path, label) {
  assert.ok(Array.isArray(path) && path.length > 0,
    `${label} path must be a nonempty Array`);
  let value = root;
  for (const component of path) {
    assert.equal(typeof component, "string", `${label} path is invalid`);
    assert.notEqual(component, "", `${label} path is invalid`);
    assert.ok(value !== null && typeof value === "object" &&
      Object.hasOwn(value, component),
    `${label} is missing ${path.join(".")}`);
    value = value[component];
  }
  return value;
}

function requireString(value, label) {
  assert.equal(typeof value, "string", `${label} must be a string`);
  assert.notEqual(value, "", `${label} must not be empty`);
  return value;
}

function requireSha256(value, label) {
  requireString(value, label);
  assert.match(value, /^[0-9a-f]{64}$/, `${label} must be lowercase SHA-256`);
  return value;
}

function normalizedStringList(value, label) {
  assert.ok(Array.isArray(value), `${label} must be an Array`);
  const result = value.map((item, index) =>
    requireString(item, `${label}[${index}]`));
  assert.equal(new Set(result).size, result.length,
    `${label} repeats a value`);
  return result;
}

function normalizedSource(role, source) {
  assert.ok(source !== null && typeof source === "object" &&
    !Array.isArray(source), `source ${role} must be an object`);
  requireString(source.commit, `source ${role} commit`);
  assert.match(source.commit, /^(?:[0-9a-f]{40}|[0-9a-f]{64})$/,
    `source ${role} commit must be a full Git object ID`);
  assert.equal(typeof source.dirty, "boolean",
    `source ${role} dirty must be Boolean`);
  const files = source.relevantFiles ?? [];
  assert.ok(Array.isArray(files),
    `source ${role} relevantFiles must be an Array`);
  const relevantFiles = files.map((file, index) => {
    assert.ok(file !== null && typeof file === "object" &&
      !Array.isArray(file), `source ${role} relevantFiles[${index}] invalid`);
    return {
      path: requireString(file.path,
        `source ${role} relevantFiles[${index}].path`),
      sha256: requireSha256(file.sha256,
        `source ${role} relevantFiles[${index}].sha256`),
    };
  });
  assert.equal(new Set(relevantFiles.map(({ path }) => path)).size,
    relevantFiles.length, `source ${role} relevantFiles repeat a path`);
  assert.ok(source.repository === undefined || source.repository === null ||
    typeof source.repository === "string",
  `source ${role} repository must be a string or null`);
  if (typeof source.repository === "string") {
    requireString(source.repository, `source ${role} repository`);
  }
  return {
    role,
    repository: source.repository ?? null,
    commit: source.commit,
    dirty: source.dirty,
    relevantFiles,
  };
}

function normalizedOperations(config, build) {
  assert.ok(Array.isArray(config.operations) && config.operations.length > 0,
    "source-package operations must be a nonempty Array");
  const operations = config.operations.map((operation, index) => {
    assert.ok(operation !== null && typeof operation === "object" &&
      !Array.isArray(operation), `source-package operation ${index} invalid`);
    const name = requireString(operation.name,
      `source-package operation ${index} name`);
    assert.ok(operation.mode === "production" || operation.mode === "diagnostic",
      `source-package operation ${name} has invalid mode`);
    const phases = normalizedStringList(operation.phases ?? [],
      `source-package operation ${name} phases`);
    return {
      name,
      mode: operation.mode,
      inputContract: requireString(operation.inputContract,
        `source-package operation ${name} input contract`),
      resultContract: requireString(operation.resultContract,
        `source-package operation ${name} result contract`),
      phases,
    };
  });
  assert.equal(new Set(operations.map(({ name }) => name)).size,
    operations.length, "source-package operations repeat a name");
  const inventory = valueAt(build, config.adapter.operationInventoryPath,
    "browser-adapter operation inventory");
  assert.deepEqual(operations.map(({ name }) => name), inventory,
    "source-package operations differ from BUILD.json");
  return operations;
}

function normalizedLeanToolchain(config, build) {
  assert.ok(config !== null && typeof config === "object" &&
    !Array.isArray(config), "source-package Lean toolchain policy invalid");
  const toolchain = requireString(valueAt(build, config.toolchainPath,
    "Lean toolchain"), "Lean toolchain");
  const description = requireString(valueAt(build, config.versionPath,
    "Lean version"), "Lean version");
  const match = /^Lean \(version ([^,]+), [^,]+, commit ([0-9a-f]{40}), [^)]+\)$/
    .exec(description);
  assert.notEqual(match, null,
    "Lean version must contain normalized version and full commit");
  return { toolchain, version: match[1], commit: match[2] };
}

function normalizedAcceptance(config) {
  assert.ok(config !== null && typeof config === "object" &&
    !Array.isArray(config), "source-package acceptance policy invalid");
  assert.ok(config.status === "accepted" || config.status === "provisional",
    "source-package acceptance status invalid");
  return {
    status: config.status,
    authority: requireString(config.authority,
      "source-package acceptance authority"),
  };
}

/**
 * Project one package-specific BUILD document into the common discovery view.
 * The result deliberately omits workload semantics, oracles, and benchmark data.
 */
export function describeSourcePackage(verification, packagePolicy) {
  const config = packagePolicy.sourcePackage;
  if (config === undefined) return null;
  assert.ok(config !== null && typeof config === "object",
    "sourcePackage policy must be an object");
  const { build, metadata, imports, exports } = verification;
  const buildFile = packagePolicy.build.file ?? "BUILD.json";
  const schemaField = packagePolicy.build.schemaField ?? "schemaVersion";
  const sources = valueAt(build, config.provenancePath ?? ["sources"],
    "source-package provenance");
  assert.ok(sources !== null && typeof sources === "object" &&
    !Array.isArray(sources), "source-package provenance must be an object");
  const provenance = Object.entries(sources)
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([role, source]) => normalizedSource(role, source));
  assert.ok(provenance.length > 0, "source-package provenance must not be empty");

  const adapter = config.adapter;
  assert.ok(adapter !== null && typeof adapter === "object",
    "source-package adapter must be an object");
  assert.ok(packagePolicy.payloadFiles.includes(adapter.file),
    "source-package adapter must be checksummed");
  const operations = normalizedOperations(config, build);
  const evidenceFiles = normalizedStringList(config.evidenceFiles ?? [],
    "source-package evidence files");
  for (const file of evidenceFiles) {
    assert.ok(packagePolicy.payloadFiles.includes(file),
      `source-package evidence file is not checksummed: ${file}`);
  }
  const ownershipCapability = valueAt(build, config.ownership.capabilityPath,
    "ownership capability");
  assert.equal(typeof config.ownership.rawAddressesExposed, "boolean",
    "source-package rawAddressesExposed must be Boolean");
  requireString(metadata.memoryOwner, "source-package memory owner");
  requireSha256(metadata.sha256, "source-package artifact SHA-256");

  return {
    schemaVersion: SOURCE_PACKAGE_DESCRIPTOR_VERSION,
    package: {
      name: packagePolicy.name,
      build: { file: buildFile, schemaField,
        schemaVersion: packagePolicy.build.schemaVersion },
      acceptance: normalizedAcceptance(config.acceptance),
    },
    provenance: { sources: provenance },
    producer: {
      project: requireString(config.producer.project,
        "source-package producer project"),
      backend: requireString(config.producer.backend,
        "source-package producer backend"),
      toolchain: {
        lean: normalizedLeanToolchain(config.producer.lean, build),
      },
      artifact: {
        file: metadata.file,
        byteLength: metadata.byteLength,
        sha256: metadata.sha256,
        imports,
        exports,
      },
      adapter: {
        file: adapter.file,
        apiVersion: requireString(valueAt(build, adapter.apiVersionPath,
          "browser-adapter API version"), "browser-adapter API version"),
        startupFields: normalizedStringList(adapter.startupFields ?? [],
          "browser-adapter startup fields"),
        initializationFields: normalizedStringList(
          adapter.initializationFields ?? [],
          "browser-adapter initialization fields"),
      },
    },
    verifier: {
      policyVersion: packagePolicy.version,
      policyName: packagePolicy.name,
      checksum: {
        algorithm: "sha256",
        manifest: "SHA256SUMS",
        payloadFiles: [...packagePolicy.payloadFiles],
      },
      smoke: packagePolicy.smokeFile,
      evidenceFiles,
    },
    operations,
    ownership: {
      capabilityVersion: requireString(ownershipCapability.version,
        "ownership capability version"),
      memoryOwner: metadata.memoryOwner,
      model: requireString(config.ownership.model,
        "source-package ownership model"),
      arena: requireString(config.ownership.arena,
        "source-package ownership arena"),
      reclamation: requireString(config.ownership.reclamation,
        "source-package ownership reclamation"),
      rawAddressesExposed: config.ownership.rawAddressesExposed,
      transfer: {
        publicInput: requireString(config.ownership.transfer?.publicInput,
          "source-package public-input transfer"),
        encodedInput: requireString(config.ownership.transfer?.encodedInput,
          "source-package encoded-input transfer"),
        output: requireString(config.ownership.transfer?.output,
          "source-package output transfer"),
      },
    },
  };
}

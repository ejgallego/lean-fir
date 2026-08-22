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
    const phases = operation.phases ?? [];
    assert.ok(Array.isArray(phases),
      `source-package operation ${name} phases must be an Array`);
    for (const [phaseIndex, phase] of phases.entries()) {
      requireString(phase,
        `source-package operation ${name} phases[${phaseIndex}]`);
    }
    assert.equal(new Set(phases).size, phases.length,
      `source-package operation ${name} repeats a phase`);
    return { name, mode: operation.mode, phases: [...phases] };
  });
  assert.equal(new Set(operations.map(({ name }) => name)).size,
    operations.length, "source-package operations repeat a name");
  const inventory = valueAt(build, config.adapter.operationInventoryPath,
    "browser-adapter operation inventory");
  assert.deepEqual(operations.map(({ name }) => name), inventory,
    "source-package operations differ from BUILD.json");
  return operations;
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
    },
    provenance: { sources: provenance },
    producer: {
      project: requireString(config.producer.project,
        "source-package producer project"),
      backend: requireString(config.producer.backend,
        "source-package producer backend"),
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
    },
  };
}

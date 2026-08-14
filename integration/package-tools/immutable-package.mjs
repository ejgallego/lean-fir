import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import {
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  realpathSync,
  renameSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { basename, dirname, join, relative } from "node:path";

const checksumLine = /^([0-9a-f]{64})  ([^/\\\0]+)$/;

export function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function requireComponent(value, label) {
  assert.equal(typeof value, "string", `${label} must be a string`);
  assert.notEqual(value, "", `${label} must not be empty`);
  assert.equal(value, basename(value), `${label} must be one path component`);
  assert.notEqual(value, ".", `${label} must not be .`);
  assert.notEqual(value, "..", `${label} must not be ..`);
  assert.equal(value.includes("\0"), false, `${label} must not contain NUL`);
  return value;
}

function requireOutputNames(outputNames) {
  assert.ok(Array.isArray(outputNames), "outputNames must be an Array");
  assert.ok(outputNames.length > 0, "outputNames must not be empty");
  const names = outputNames.map((name, index) =>
    requireComponent(name, `outputNames[${index}]`));
  assert.equal(new Set(names).size, names.length,
    "outputNames must not contain duplicates");
  assert.equal(names.includes("SHA256SUMS"), false,
    "SHA256SUMS is managed by the immutable package publisher");
  return names;
}

export function checksumManifest(directory, outputNames) {
  const names = requireOutputNames(outputNames);
  return names.map((name) =>
    `${sha256(readFileSync(join(directory, name)))}  ${name}`).join("\n") + "\n";
}

export function verifyChecksumManifest(directory, outputNames) {
  const names = requireOutputNames(outputNames);
  const packageNames = [...names, "SHA256SUMS"];
  assert.deepEqual(readdirSync(directory).sort(), packageNames.toSorted(),
    "package file inventory differs from outputNames plus SHA256SUMS");
  for (const name of packageNames) {
    assert.equal(lstatSync(join(directory, name)).isFile(), true,
      `${name} must be a regular file`);
  }
  const text = readFileSync(join(directory, "SHA256SUMS"), "utf8");
  assert.ok(text.endsWith("\n"), "SHA256SUMS must end with a newline");
  const lines = text.slice(0, -1).split("\n");
  const entries = lines.map((line, index) => {
    const match = checksumLine.exec(line);
    assert.ok(match, `invalid SHA256SUMS line ${index + 1}`);
    return { digest: match[1], name: match[2] };
  });
  assert.deepEqual(entries.map(({ name }) => name), names,
    "SHA256SUMS file inventory differs from outputNames");
  for (const { digest, name } of entries) {
    assert.equal(sha256(readFileSync(join(directory, name))), digest,
      `checksum mismatch for ${name}`);
  }
  return text;
}

function replaceCurrentLink(current, destination) {
  const parent = dirname(current);
  const temporary = join(parent, `.${basename(current)}-${process.pid}`);
  rmSync(temporary, { force: true });
  try {
    symlinkSync(relative(parent, destination), temporary);
    renameSync(temporary, current);
  } finally {
    rmSync(temporary, { force: true });
  }
  assert.equal(lstatSync(current).isSymbolicLink(), true,
    `${current} must be a symbolic link`);
  assert.equal(realpathSync(current), realpathSync(destination),
    `${current} does not resolve to the published package`);
}

export function publishImmutablePackage({
  packagesDirectory,
  packageId,
  outputNames,
  populate,
  currentLink = null,
}) {
  assert.equal(typeof packagesDirectory, "string",
    "packagesDirectory must be a string");
  assert.equal(typeof populate, "function", "populate must be a function");
  requireComponent(packageId, "packageId");
  const names = requireOutputNames(outputNames);
  const destination = join(packagesDirectory, packageId);
  const staging = join(packagesDirectory,
    `.staging-${packageId}-${process.pid}`);

  mkdirSync(packagesDirectory, { recursive: true });
  rmSync(staging, { recursive: true, force: true });
  mkdirSync(staging);
  try {
    populate(staging);
    const sums = checksumManifest(staging, names);
    writeFileSync(join(staging, "SHA256SUMS"), sums);
    verifyChecksumManifest(staging, names);

    if (existsSync(destination)) {
      for (const name of [...names, "SHA256SUMS"]) {
        assert.deepEqual(readFileSync(join(staging, name)),
          readFileSync(join(destination, name)),
          `immutable package ${packageId} differs at ${name}`);
      }
    } else {
      renameSync(staging, destination);
    }
  } finally {
    rmSync(staging, { recursive: true, force: true });
  }

  verifyChecksumManifest(destination, names);
  if (currentLink !== null) {
    assert.equal(typeof currentLink, "string", "currentLink must be a string");
    replaceCurrentLink(currentLink, destination);
  }
  return { directory: destination };
}

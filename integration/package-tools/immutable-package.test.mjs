import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync,
  writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import {
  checksumManifest,
  publishImmutablePackage,
  sha256,
  verifyChecksumManifest,
} from "./immutable-package.mjs";

function withDirectory(run) {
  const directory = mkdtempSync(join(tmpdir(), "fir-immutable-package-"));
  try {
    return run(directory);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

const outputNames = ["BUILD.json", "module.wasm", "smoke.mjs"];

function populate(bytes = Buffer.from([0, 97, 115, 109])) {
  return (directory) => {
    writeFileSync(join(directory, "BUILD.json"), "{\"format\":1}\n");
    writeFileSync(join(directory, "module.wasm"), bytes);
    writeFileSync(join(directory, "smoke.mjs"), "export default true;\n");
  };
}

test("publishes, verifies, and atomically selects an immutable package", () =>
  withDirectory((root) => {
    const packagesDirectory = join(root, "packages");
    const currentLink = join(root, "current");
    const result = publishImmutablePackage({
      packagesDirectory,
      packageId: "fixture-v1",
      outputNames,
      populate: populate(),
      currentLink,
    });
    assert.equal(result.directory, join(packagesDirectory, "fixture-v1"));
    assert.equal(realpathSync(currentLink), realpathSync(result.directory));
    const expected = outputNames.map((name) =>
      `${sha256(readFileSync(join(result.directory, name)))}  ${name}`)
      .join("\n") + "\n";
    assert.equal(readFileSync(join(result.directory, "SHA256SUMS"), "utf8"),
      expected);
    assert.equal(checksumManifest(result.directory, outputNames), expected);
    assert.equal(verifyChecksumManifest(result.directory, outputNames), expected);

    const replacement = publishImmutablePackage({
      packagesDirectory,
      packageId: "fixture-v2",
      outputNames,
      populate: populate(Buffer.from([1, 97, 115, 109])),
      currentLink,
    });
    assert.equal(realpathSync(currentLink), realpathSync(replacement.directory));
    assert.deepEqual(readFileSync(join(result.directory, "module.wasm")),
      Buffer.from([0, 97, 115, 109]));
  }));

test("reuses an identical package and rejects an identity collision", () =>
  withDirectory((root) => {
    const packagesDirectory = join(root, "packages");
    const options = {
      packagesDirectory,
      packageId: "fixture-v1",
      outputNames,
      populate: populate(),
    };
    const first = publishImmutablePackage(options);
    const second = publishImmutablePackage(options);
    assert.equal(second.directory, first.directory);
    assert.throws(() => publishImmutablePackage({
      ...options,
      populate: populate(Buffer.from([1, 97, 115, 109])),
    }), /immutable package fixture-v1 differs at module\.wasm/);
    assert.deepEqual(readFileSync(join(first.directory, "module.wasm")),
      Buffer.from([0, 97, 115, 109]));
    assert.deepEqual(readdirSync(packagesDirectory), ["fixture-v1"]);
  }));

test("detects tampering and rejects unsafe inventories", () =>
  withDirectory((root) => {
    const result = publishImmutablePackage({
      packagesDirectory: join(root, "packages"),
      packageId: "fixture-v1",
      outputNames,
      populate: populate(),
    });
    writeFileSync(join(result.directory, "module.wasm"), "changed");
    assert.throws(() => verifyChecksumManifest(result.directory, outputNames),
      /checksum mismatch for module\.wasm/);
    assert.throws(() => publishImmutablePackage({
      packagesDirectory: join(root, "packages"),
      packageId: "../escape",
      outputNames,
      populate: populate(),
    }), /packageId must be one path component/);
    assert.throws(() => checksumManifest(result.directory,
      ["BUILD.json", "../module.wasm"]),
    /outputNames\[1\] must be one path component/);
    assert.throws(() => publishImmutablePackage({
      packagesDirectory: join(root, "packages"),
      packageId: "fixture-extra",
      outputNames,
      populate(directory) {
        populate()(directory);
        writeFileSync(join(directory, "unchecksummed.txt"), "extra\n");
      },
    }), /package file inventory differs/);
    assert.equal(readdirSync(join(root, "packages"))
      .includes("fixture-extra"), false);
  }));

test("runs validation before publishing or replacing the current link", () =>
  withDirectory((root) => {
    const packagesDirectory = join(root, "packages");
    const currentLink = join(root, "current");
    const accepted = publishImmutablePackage({
      packagesDirectory,
      packageId: "accepted-v1",
      outputNames,
      populate: populate(),
      currentLink,
      validate(directory) {
        assert.equal(readFileSync(join(directory, "BUILD.json"), "utf8"),
          "{\"format\":1}\n");
      },
    });
    assert.equal(realpathSync(currentLink), realpathSync(accepted.directory));

    assert.throws(() => publishImmutablePackage({
      packagesDirectory,
      packageId: "rejected-v2",
      outputNames,
      populate: populate(Buffer.from([1, 97, 115, 109])),
      currentLink,
      validate() {
        throw new Error("policy rejected package");
      },
    }), /policy rejected package/);
    assert.equal(realpathSync(currentLink), realpathSync(accepted.directory));
    assert.equal(readdirSync(packagesDirectory).includes("rejected-v2"), false);
  }));

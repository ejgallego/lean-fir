import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";

import {
  packageFiles,
  parseExportArguments,
  payloadFiles,
  publishCatalogPackage,
  validateSourceCheckouts,
} from "./export-raw-package.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const exporter = join(directory, "export-raw-package.mjs");

function withDirectory(run) {
  const root = mkdtempSync(join(tmpdir(), "fir-lean-zip-export-"));
  try {
    return run(root);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

function git(root, args) {
  return execFileSync("git", ["-C", root, ...args], {
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
  }).trim();
}

function repository(path, label) {
  mkdirSync(path);
  git(path, ["init", "-q"]);
  writeFileSync(join(path, `${label}.txt`), `${label}\n`);
  git(path, ["add", "."]);
  git(path, ["-c", "user.name=FIR Test", "-c",
    "user.email=fir-test@example.invalid", "commit", "-q", "-m", label]);
  return git(path, ["rev-parse", "HEAD"]);
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
}

function packageFixture(path, sources, smoke = "process.exit(0);\n") {
  mkdirSync(path);
  const build = {
    schemaVersion: "fir.lean-zip.raw.build/v3",
    sources: {
      fir: { commit: sources.producer.commit, dirty: false },
      leanZip: { commit: sources.client.commit, dirty: false },
      zipCommon: { commit: sources.zipCommon.commit, dirty: false },
    },
    entry: {
      sourceName: "Zip.Wasm.compressRaw",
      levels: Array.from({ length: 10 }, (_, index) => index + 1),
    },
    wasm: {
      functionImportCount: 0,
      memoryImportCount: 0,
      memoryOwner: "module",
    },
  };
  const contents = new Map([
    ["BUILD.json", `${JSON.stringify(build)}\n`],
    ["lean-zip-byte-array-browser-adapter.mjs", "export {};\n"],
    ["lean-zip-raw-browser-adapter.mjs", "export {};\n"],
    ["standard-math-runtime-contract.mjs", "export {};\n"],
    ["lean-zip-raw.wasm", Buffer.from([0, 97, 115, 109])],
    ["lean-zip-raw.wasm.functions.json", "{\"functions\":[]}\n"],
    ["lean-zip-raw.wasm.json", "{\"imports\":[]}\n"],
    ["smoke.mjs", smoke],
  ]);
  for (const [name, value] of contents) writeFileSync(join(path, name), value);
  const sums = payloadFiles.map((name) =>
    `${sha256(readFileSync(join(path, name)))}  ${name}`).join("\n") + "\n";
  writeFileSync(join(path, "SHA256SUMS"), sums);
}

test("parses the exact generic catalog surface", () => {
  assert.deepEqual(parseExportArguments([
    "--output", "/controlled/out",
    "--checkout", "producer=/fir",
    "--checkout", "client=/lean-zip",
    "--checkout", "zip-common=/zip-common",
  ]), {
    output: "/controlled/out",
    checkouts: {
      producer: "/fir",
      client: "/lean-zip",
      "zip-common": "/zip-common",
    },
  });
});

test("ships an executable regular-file entry point", () => {
  const state = lstatSync(exporter);
  assert.equal(state.isFile(), true);
  assert.notEqual(state.mode & 0o111, 0);
  const help = execFileSync(exporter, ["--help"], { encoding: "utf8" });
  assert.match(help, /--checkout producer=EXACT_CLEAN_FIR_CHECKOUT/);
  assert.match(help, /--checkout client=EXACT_CLEAN_LEAN_ZIP_CHECKOUT/);
  assert.match(help, /--checkout zip-common=EXACT_CLEAN_ZIP_COMMON_CHECKOUT/);
});

test("rejects package arguments, unknown roles, and missing roles", () => {
  assert.throws(() => parseExportArguments([
    "--output", "/out", "--package", "runtime=/package",
  ]), /accepts no dependency packages/);
  assert.throws(() => parseExportArguments([
    "--output", "/out", "--package=runtime=/package",
  ]), /accepts no dependency packages/);
  assert.throws(() => parseExportArguments([
    "--output", "/out", "--checkout", "other=/other",
  ]), /unknown checkout role/);
  assert.throws(() => parseExportArguments([
    "--output", "/out", "--checkout", "producer=/fir",
    "--checkout", "client=/client",
  ]), /zip-common=.* is required/);
});

test("requires exact clean producer and pinned client checkouts", () =>
  withDirectory((root) => {
    const producer = join(root, "producer");
    const client = join(root, "client");
    const zipCommon = join(root, "zip-common");
    const other = join(root, "other");
    const producerRevision = repository(producer, "producer");
    const clientRevision = repository(client, "client");
    const zipCommonRevision = repository(zipCommon, "zip-common");
    repository(other, "other");

    const accepted = validateSourceCheckouts({
      producer,
      client,
      zipCommon,
      expectedProducerRoot: producer,
      expectedClientRevision: clientRevision,
      expectedZipCommonRevision: zipCommonRevision,
    });
    assert.equal(accepted.producer.commit, producerRevision);
    assert.throws(() => validateSourceCheckouts({
      producer: other,
      client,
      zipCommon,
      expectedProducerRoot: producer,
      expectedClientRevision: clientRevision,
      expectedZipCommonRevision: zipCommonRevision,
    }), /producer checkout must contain this exporter/);
    assert.throws(() => validateSourceCheckouts({
      producer,
      client,
      zipCommon,
      expectedProducerRoot: producer,
      expectedClientRevision: "0".repeat(40),
      expectedZipCommonRevision: zipCommonRevision,
    }), /client revision mismatch/);
    writeFileSync(join(zipCommon, "dirty.txt"), "dirty\n");
    assert.throws(() => validateSourceCheckouts({
      producer,
      client,
      zipCommon,
      expectedProducerRoot: producer,
      expectedClientRevision: clientRevision,
      expectedZipCommonRevision: zipCommonRevision,
    }), /zip-common checkout must be clean/);
  }));

test("publishes only regular files through caller-controlled staging", () =>
  withDirectory((root) => {
    const parent = join(root, "caller");
    mkdirSync(parent);
    const output = join(parent, "output");
    const sources = {
      producer: { commit: "1".repeat(40) },
      client: { commit: "2".repeat(40) },
      zipCommon: { commit: "3".repeat(40) },
    };
    let observedWorkspace;
    const published = publishCatalogPackage({
      outputDirectory: output,
      sources,
      runProducer: ({ destination, workspace }) => {
        observedWorkspace = workspace;
        packageFixture(destination, sources);
      },
    });
    assert.equal(published, output);
    assert.equal(dirname(observedWorkspace), parent);
    assert.deepEqual(readdirSync(output).sort(), [...packageFiles].sort());
    for (const name of packageFiles) {
      assert.equal(lstatSync(join(output, name)).isFile(), true);
      assert.equal(lstatSync(join(output, name)).isSymbolicLink(), false);
    }
    assert.throws(() => publishCatalogPackage({
      outputDirectory: output,
      sources,
      runProducer: () => assert.fail("producer must not run"),
    }), /output directory must be fresh/);
  }));

test("rejects symbolic output and removes a failed publication", () =>
  withDirectory((root) => {
    const target = join(root, "target");
    mkdirSync(target);
    const symbolic = join(root, "symbolic");
    symlinkSync(target, symbolic);
    const sources = {
      producer: { commit: "1".repeat(40) },
      client: { commit: "2".repeat(40) },
      zipCommon: { commit: "3".repeat(40) },
    };
    assert.throws(() => publishCatalogPackage({
      outputDirectory: symbolic,
      sources,
      runProducer: () => assert.fail("producer must not run"),
    }), /output directory must be fresh/);

    const failed = join(root, "failed");
    assert.throws(() => publishCatalogPackage({
      outputDirectory: failed,
      sources,
      runProducer: ({ destination }) =>
        packageFixture(destination, sources, "process.exit(1);\n"),
    }), /Command failed/);
    assert.throws(() => lstatSync(failed), /ENOENT/);
  }));

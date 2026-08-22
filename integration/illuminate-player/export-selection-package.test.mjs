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
  publishAcceptedPackage,
  validateSourceCheckouts,
} from "./export-selection-package.mjs";
import {
  selectionExpectedExports,
  selectionPackagePolicy,
} from "./selection-package-policy.mjs";

const directory = dirname(fileURLToPath(import.meta.url));
const exporter = join(directory, "export-selection-package.mjs");

function withDirectory(run) {
  const root = mkdtempSync(join(tmpdir(), "fir-selection-export-"));
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

function unsignedLeb(value) {
  const bytes = [];
  do {
    const next = value & 0x7f;
    value >>>= 7;
    bytes.push(value === 0 ? next : next | 0x80);
  } while (value !== 0);
  return bytes;
}

function section(id, contents) {
  return [id, ...unsignedLeb(contents.length), ...contents];
}

function stringBytes(value) {
  const bytes = [...Buffer.from(value, "utf8")];
  return [...unsignedLeb(bytes.length), ...bytes];
}

function selectionWasm() {
  const functions = selectionExpectedExports
    .filter(({ kind }) => kind === "function");
  const types = section(1, [1, 0x60, 0, 0]);
  const declarations = section(3,
    [...unsignedLeb(functions.length), ...functions.map(() => 0)]);
  const memory = section(5, [1, 0, 1]);
  const exports = section(7, [
    ...unsignedLeb(selectionExpectedExports.length),
    ...selectionExpectedExports.flatMap(({ name, kind }, index) => [
      ...stringBytes(name),
      kind === "function" ? 0 : 2,
      kind === "function" ? index : 0,
    ]),
  ]);
  const code = section(10, [
    ...unsignedLeb(functions.length),
    ...functions.flatMap(() => [2, 0, 0x0b]),
  ]);
  return Buffer.from([
    0, 0x61, 0x73, 0x6d, 1, 0, 0, 0,
    ...types, ...declarations, ...memory, ...exports, ...code,
  ]);
}

function packageFixture(path, smoke = "process.exit(0);\n") {
  mkdirSync(path);
  const wasm = selectionWasm();
  const build = {
    schemaVersion: selectionPackagePolicy.build.schemaVersion,
    wasm: {
      file: "illuminate-selection-player.wasm",
      byteLength: wasm.byteLength,
      sha256: sha256(wasm),
      functionImportCount: 0,
      memoryImportCount: 0,
      memoryOwner: "module",
      memoryExports: ["memory"],
      functionExportCount: 7,
    },
    capabilities: {
      completeRuntime: {
        version: "fir.illuminate-player.complete-runtime/v2",
        selfContained: true,
        residentRuntime: {
          version: "fir.closed-resident-runtime/v1",
          provider: "none",
          externalDeclarations: [],
        },
      },
      browserAdapter: { apiVersion: "fir.illuminate-player.browser/v5" },
      hotEvent: { version: "fir.illuminate-player.hot-event/v2" },
      inputLayout: {
        version: "lean-4.33-Illuminate.Animation.SelectionAnimation/v4",
      },
      ownership: {
        version: "fir.illuminate-player.persistent-checkpoint/v3",
      },
    },
  };
  const contents = new Map([
    ["BUILD.json", `${JSON.stringify(build)}\n`],
    ["illuminate-selection-player-browser-adapter.mjs", "export {};\n"],
    ["illuminate-selection-player.wasm", wasm],
    ["illuminate-selection-player.wasm.json",
      "{\"imports\":[],\"completeRuntime\":true}\n"],
    ["smoke.mjs", smoke],
  ]);
  for (const [name, value] of contents) writeFileSync(join(path, name), value);
  const sums = payloadFiles.map((name) =>
    `${sha256(readFileSync(join(path, name)))}  ${name}`).join("\n") + "\n";
  writeFileSync(join(path, "SHA256SUMS"), sums);
}

test("parses the generic catalog command and direct-use alias", () => {
  assert.deepEqual(parseExportArguments([
    "--output", "/tmp/out",
    "--checkout", "producer=/tmp/fir",
    "--checkout", "illuminate=/tmp/illuminate",
  ]), {
    mode: "catalog",
    output: "/tmp/out",
    checkouts: { producer: "/tmp/fir", illuminate: "/tmp/illuminate" },
  });
  assert.deepEqual(parseExportArguments(["/tmp/out"], {
    ILLUMINATE_ROOT: "/tmp/illuminate",
  }), {
    mode: "direct-alias",
    output: "/tmp/out",
    checkouts: { producer: null, illuminate: "/tmp/illuminate" },
  });
});

test("ships an executable regular-file catalog entry point", () => {
  const state = lstatSync(exporter);
  assert.equal(state.isFile(), true);
  assert.notEqual(state.mode & 0o111, 0);
  const help = execFileSync(exporter, ["--help"], { encoding: "utf8" });
  assert.match(help, /--checkout producer=EXACT_CLEAN_FIR_CHECKOUT/);
  assert.match(help, /--checkout illuminate=EXACT_CLEAN_ILLUMINATE_CHECKOUT/);
});

test("rejects unknown roles, dependency packages, and incomplete commands", () => {
  assert.throws(() => parseExportArguments([
    "--output", "/tmp/out", "--checkout", "other=/tmp/other",
  ]), /unknown checkout role/);
  assert.throws(() => parseExportArguments([
    "--output", "/tmp/out", "--package", "dependency=/tmp/package",
  ]), /accepts no dependency packages/);
  assert.throws(() => parseExportArguments([
    "--output", "/tmp/out", "--package=dependency=/tmp/package",
  ]), /accepts no dependency packages/);
  assert.throws(() => parseExportArguments([
    "--output", "/tmp/out", "--checkout", "producer=/tmp/fir",
  ]), /illuminate=.* is required/);
});

test("requires exact clean producer and pinned Illuminate checkouts", () =>
  withDirectory((root) => {
    const producer = join(root, "producer");
    const illuminate = join(root, "illuminate");
    const other = join(root, "other");
    repository(producer, "producer");
    const illuminateRevision = repository(illuminate, "illuminate");
    repository(other, "other");

    const accepted = validateSourceCheckouts({
      producer,
      illuminate,
      expectedProducerRoot: producer,
      expectedIlluminateRevision: illuminateRevision,
    });
    assert.equal(accepted.illuminate.commit, illuminateRevision);
    assert.throws(() => validateSourceCheckouts({
      producer: other,
      illuminate,
      expectedProducerRoot: producer,
      expectedIlluminateRevision: illuminateRevision,
    }), /producer checkout must contain this exporter/);
    assert.throws(() => validateSourceCheckouts({
      producer,
      illuminate,
      expectedProducerRoot: producer,
      expectedIlluminateRevision: "0".repeat(40),
    }), /illuminate revision mismatch/);

    writeFileSync(join(producer, "dirty.txt"), "dirty\n");
    assert.throws(() => validateSourceCheckouts({
      producer,
      illuminate,
      expectedProducerRoot: producer,
      expectedIlluminateRevision: illuminateRevision,
    }), /producer checkout must be clean/);
    rmSync(join(producer, "dirty.txt"));
    writeFileSync(join(illuminate, "dirty.txt"), "dirty\n");
    assert.throws(() => validateSourceCheckouts({
      producer,
      illuminate,
      expectedProducerRoot: producer,
      expectedIlluminateRevision: illuminateRevision,
    }), /illuminate checkout must be clean/);
  }));

test("publishes exactly six regular files into a fresh output", () =>
  withDirectory((root) => {
    const source = join(root, "source");
    const output = join(root, "output");
    packageFixture(source);
    assert.equal(publishAcceptedPackage({
      sourceDirectory: source,
      outputDirectory: output,
    }), output);
    assert.deepEqual(readdirSync(output).sort(), [...packageFiles].sort());
    for (const name of packageFiles) {
      assert.equal(lstatSync(join(output, name)).isFile(), true);
      assert.equal(lstatSync(join(output, name)).isSymbolicLink(), false);
    }
    assert.throws(() => publishAcceptedPackage({
      sourceDirectory: source,
      outputDirectory: output,
    }), /output directory must be fresh/);
  }));

test("rejects symbolic output, checksum mismatch, and smoke failure", () =>
  withDirectory((root) => {
    const source = join(root, "source");
    packageFixture(source);
    const target = join(root, "target");
    mkdirSync(target);
    const symbolic = join(root, "symbolic");
    symlinkSync(target, symbolic);
    assert.throws(() => publishAcceptedPackage({
      sourceDirectory: source,
      outputDirectory: symbolic,
    }), /output directory must be fresh/);

    writeFileSync(join(source, "BUILD.json"), "tampered\n");
    const mismatched = join(root, "mismatched");
    assert.throws(() => publishAcceptedPackage({
      sourceDirectory: source,
      outputDirectory: mismatched,
    }), /checksum mismatch for BUILD\.json/);
    assert.throws(() => lstatSync(mismatched), /ENOENT/);

    rmSync(source, { recursive: true });
    packageFixture(source, "process.exit(1);\n");
    const failedSmoke = join(root, "failed-smoke");
    assert.throws(() => publishAcceptedPackage({
      sourceDirectory: source,
      outputDirectory: failedSmoke,
    }), /Command failed/);
    assert.throws(() => lstatSync(failedSmoke), /ENOENT/);
  }));

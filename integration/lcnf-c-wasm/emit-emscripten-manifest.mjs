import { createHash } from "node:crypto";
import { readFile, stat, writeFile } from "node:fs/promises";
import {
  basename,
  dirname,
  isAbsolute,
  relative,
  resolve,
  sep,
} from "node:path";

function fail(message) {
  throw new Error(`emit-emscripten-manifest.mjs: ${message}`);
}

function takeValue(args, index, option) {
  const value = args[index + 1];
  if (value === undefined) {
    fail(`${option} requires a value`);
  }
  return value;
}

function sourceId(root, source) {
  const path = relative(root, source);
  if (path === "" || isAbsolute(path) || path === ".." || path.startsWith(`..${sep}`)) {
    fail(`source is outside the Lean root: ${source}`);
  }
  return path.split(sep).join("/");
}

async function artifactRecord(manifestPath, artifactPath) {
  if (dirname(manifestPath) !== dirname(artifactPath)) {
    fail(`artifact must be emitted beside the manifest: ${artifactPath}`);
  }
  const [bytes, metadata] = await Promise.all([
    readFile(artifactPath),
    stat(artifactPath),
  ]);
  return {
    file: basename(artifactPath),
    byteLength: metadata.size,
    sha256: createHash("sha256").update(bytes).digest("hex"),
  };
}

const options = {
  exports: [],
  extraSources: [],
  extraCSources: [],
  runtimeMethods: [],
  compileFlags: [],
  linkFlags: [],
};
const args = process.argv.slice(2);

for (let index = 0; index < args.length; index += 1) {
  const option = args[index];
  const value = takeValue(args, index, option);
  index += 1;
  switch (option) {
    case "--out":
      options.out = value;
      break;
    case "--module":
      options.module = value;
      break;
    case "--wasm":
      options.wasm = value;
      break;
    case "--name":
      options.name = value;
      break;
    case "--root":
      options.root = value;
      break;
    case "--entry":
      options.entry = value;
      break;
    case "--extra-source":
      options.extraSources.push(value);
      break;
    case "--extra-c-source":
      options.extraCSources.push(value);
      break;
    case "--initializer":
      options.initializer = value;
      break;
    case "--export":
      options.exports.push(value);
      break;
    case "--runtime-method":
      options.runtimeMethods.push(value);
      break;
    case "--start":
      options.start = value;
      break;
    case "--lean-version":
      options.leanVersion = value;
      break;
    case "--lean-commit":
      options.leanCommit = value;
      break;
    case "--emscripten-version":
      options.emscriptenVersion = value;
      break;
    case "--emscripten-commit":
      options.emscriptenCommit = value;
      break;
    case "--compile-flag":
      options.compileFlags.push(value);
      break;
    case "--link-flag":
      options.linkFlags.push(value);
      break;
    default:
      fail(`unknown option: ${option}`);
  }
}

for (const required of [
  "out",
  "module",
  "wasm",
  "name",
  "root",
  "entry",
  "initializer",
  "leanVersion",
  "leanCommit",
  "emscriptenVersion",
  "emscriptenCommit",
]) {
  if (options[required] === undefined) {
    fail(`missing --${required.replace(/[A-Z]/g, (letter) => `-${letter.toLowerCase()}`)}`);
  }
}

const out = resolve(options.out);
const modulePath = resolve(options.module);
const wasmPath = resolve(options.wasm);
const root = resolve(options.root);
const entry = resolve(options.entry);
const extraSources = options.extraSources.map((source) => resolve(source));
const extraCSources = options.extraCSources.map((source) => resolve(source));
const [moduleArtifact, wasmArtifact] = await Promise.all([
  artifactRecord(out, modulePath),
  artifactRecord(out, wasmPath),
]);

const manifest = {
  schemaVersion: 1,
  profile: "emscripten",
  artifactName: options.name,
  pipeline: "lean-final-impure-lcnf-to-c-to-wasm",
  sources: {
    entry: sourceId(root, entry),
    additional: extraSources.map((source) => sourceId(root, source)),
    c: extraCSources.map((source) => sourceId(root, source)),
  },
  toolchain: {
    lean: {
      version: options.leanVersion,
      commit: options.leanCommit,
    },
    emscripten: {
      version: options.emscriptenVersion,
      commit: options.emscriptenCommit,
    },
  },
  build: {
    compileFlags: options.compileFlags,
    linkFlags: options.linkFlags,
    runtimeArchives: ["libleanrt.a", "libInit.a", "libStd.a"],
    exactFloatingPoint: true,
  },
  runtime: {
    threads: true,
    wasmExceptions: true,
    memoryGrowth: true,
    environments: ["node", "web"],
  },
  abi: {
    initialize: "fir_lcnf_c_initialize",
    moduleInitializer: options.initializer,
    exports: options.exports,
    runtimeMethods: options.runtimeMethods,
    start: options.start ?? null,
  },
  artifacts: {
    module: moduleArtifact,
    wasm: wasmArtifact,
  },
};

await writeFile(out, `${JSON.stringify(manifest, null, 2)}\n`);

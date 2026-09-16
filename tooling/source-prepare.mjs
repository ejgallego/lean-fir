import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
  chmodSync, copyFileSync, existsSync, lstatSync, mkdirSync,
  readFileSync, readdirSync, realpathSync, writeFileSync,
} from "node:fs";
import { dirname, isAbsolute, join, relative, resolve, sep } from "node:path";
import { constants } from "node:os";
import { fileURLToPath } from "node:url";
import { sha256 } from "../integration/package-tools/immutable-package.mjs";
import { makeToolingTemporaryDirectory } from "./worktree-temp.mjs";

const ignored = new Set([".git", ".lake", ".beam", ".deps", "_build"]);
const inside = (root, path) => {
  const rel = relative(root, path);
  return rel === "" || (rel !== ".." && !rel.startsWith(`..${sep}`) && !isAbsolute(rel));
};
const json = (path) => JSON.parse(readFileSync(path, "utf8"));
const save = (path, value) => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`);
export function fileIdentity(path) {
  const bytes = readFileSync(path);
  return { sha256: sha256(bytes), byteLength: bytes.length, mode: lstatSync(path).mode & 0o777 };
}

// Inputs are trusted Lake projects, not a sandbox for hostile executable configs.
// Symlinks are rejected rather than silently importing unsupplied source bytes.
export function sourceIdentity(root) {
  const files = {};
  function visit(directory, prefix = "") {
    for (const name of readdirSync(directory).sort()) {
      if (ignored.has(name)) continue;
      const path = join(directory, name);
      const rel = prefix ? `${prefix}/${name}` : name;
      const stat = lstatSync(path);
      assert(!stat.isSymbolicLink(), `source symlink is unsupported: ${path}`);
      if (stat.isDirectory()) visit(path, rel);
      else {
        assert(stat.isFile(), `source input is not a regular file: ${path}`);
        files[rel] = fileIdentity(path);
      }
    }
  }
  visit(root);
  return files;
}

function copySource(source, destination, identity) {
  mkdirSync(destination, { recursive: true, mode: 0o700 });
  for (const [rel, metadata] of Object.entries(identity)) {
    const target = join(destination, rel);
    mkdirSync(dirname(target), { recursive: true, mode: 0o700 });
    copyFileSync(join(source, rel), target);
    chmodSync(target, metadata.mode);
  }
  assert.deepEqual(sourceIdentity(destination), identity, "private source copy changed");
}

function packageName(value) {
  assert.equal(typeof value, "string", "package name must be a string");
  const name = value.replace(/^«(.*)»$/, "$1");
  assert.match(name, /^[A-Za-z0-9_.-]+$/, "unsupported package name");
  return name;
}

// Upstream setup contents stay intact; this is evidence, not a replacement setup.
export function setupIdentities(setup, project, permittedRoots) {
  const artifacts = [];
  const plugins = [];
  function record(path, kind) {
    assert.equal(typeof path, "string", "invalid setup artifact path");
    const absolute = realpathSync(resolve(project, path));
    assert(permittedRoots.some((root) => inside(realpathSync(root), absolute)),
      `setup consumes unsupplied artifact: ${absolute}`);
    const identity = { path: absolute, ...fileIdentity(absolute) };
    (kind === "plugin" ? plugins : artifacts).push(identity);
  }
  function flatten(value) {
    if (typeof value === "string") record(value, "artifact");
    else if (Array.isArray(value)) value.forEach(flatten);
    else if (value && typeof value === "object") Object.values(value).forEach(flatten);
    else assert(value === null || value === undefined, "invalid importArts value");
  }
  flatten(setup.importArts);
  for (const plugin of setup.plugins ?? []) record(plugin.path, "plugin");
  for (const path of setup.dynlibs ?? []) record(path, "artifact");
  return { artifacts, plugins };
}

export function prepareSource(options, run = spawnSync) {
  const workspace = makeToolingTemporaryDirectory("source-prepare-");
  const tmp = join(workspace, "tmp");
  const bin = join(workspace, "bin");
  mkdirSync(tmp, { mode: 0o700 });
  mkdirSync(bin, { mode: 0o700 });
  const log = join(workspace, "lake.log");
  const inputs = [];
  const preservedMaps = [];
  let result;
  let failure;
  try {
    const toolchain = realpathSync(options.toolchainDirectory);
    assert.match(options.leanCommit, /^[0-9a-f]{40}$/, "exact 40-character Lean commit required");
    const lean = join(toolchain, "bin", "lean");
    const lake = join(toolchain, "bin", "lake");
    assert(existsSync(lean) && existsSync(lake), "supplied toolchain needs bin/lean and bin/lake");
    const env = { ...process.env, TMPDIR: tmp,
      LAKE_CACHE_DIR: join(workspace, "cache"), LAKE_ARTIFACT_CACHE: "false", LAKE_RESTORE_ARTIFACTS: "false",
      PATH: `${bin}:${join(toolchain, "bin")}:${process.env.PATH}`,
      GIT_CONFIG_COUNT: "1", GIT_CONFIG_KEY_0: "protocol.allow", GIT_CONFIG_VALUE_0: "never" };
    function invoke(command, args, cwd) {
      const child = run(command, args, { cwd, env, encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });
      const output = `${child.stdout ?? ""}${child.stderr ?? ""}`;
      writeFileSync(log, output, { flag: "a" });
      if (options.verbose) process.stderr.write(output);
      if (child.error || child.signal || child.status !== 0) {
        const error = new Error(`child failed: ${child.error?.message ?? child.signal ?? child.status}`);
        error.exitCode = child.status > 0 ? child.status :
          (child.signal && constants.signals[child.signal] ? 128 + constants.signals[child.signal] : 1);
        throw error;
      }
      return child.stdout;
    }
    const version = invoke(lean, ["--version"], workspace).trim();
    assert(version.includes(options.leanCommit), `Lean commit mismatch: ${version}`);
    assert(Array.isArray(options.modules) && options.modules.length > 0, "at least one module root required");
    for (const name of [...options.modules, ...(options.entries ?? [])]) {
      assert.match(name, /^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/, "unsupported module/entry name");
    }
    const source = realpathSync(options.source);
    preservedMaps.push({ path: resolve(options.packages), before: fileIdentity(options.packages) });
    const paths = json(options.packages);
    assert(paths && typeof paths === "object" && !Array.isArray(paths), "packages must be a path-only object");
    const project = join(workspace, "project");
    function supply(original, prepared) {
      const before = sourceIdentity(original);
      inputs.push({ original, prepared, before });
      copySource(original, prepared, before);
    }
    supply(source, project);
    const dependencies = new Map();
    for (const [name, path] of Object.entries(paths)) {
      assert.equal(typeof path, "string", "dependency map values must be paths only");
      const normalized = packageName(name);
      assert(!dependencies.has(normalized), "duplicate dependency name");
      const original = realpathSync(resolve(dirname(resolve(options.packages)), path));
      const prepared = join(workspace, "dependencies", normalized);
      supply(original, prepared);
      dependencies.set(normalized, prepared);
    }
    const manifest = json(join(project, "lake-manifest.json"));
    const packages = new Map();
    for (const input of inputs) {
      const manifestPath = join(input.prepared, "lake-manifest.json");
      if (!existsSync(manifestPath)) continue;
      for (const dependency of json(manifestPath).packages ?? []) {
        const name = packageName(dependency.name);
        assert(dependencies.has(name), `missing supplied dependency: ${name}`);
        const target = dependencies.get(name);
        const config = dependency.configFile ?? (existsSync(join(target, "lakefile.lean")) ? "lakefile.lean" : "lakefile.toml");
        assert(inside(target, resolve(target, config)) && existsSync(join(target, config)), `missing dependency configuration: ${name}`);
        const mapped = { ...dependency, type: "path", dir: target };
        for (const key of ["url", "rev", "inputRev", "subDir"]) delete mapped[key];
        if (packages.has(name)) {
          assert.equal(packages.get(name).dir, mapped.dir, "inconsistent dependency path");
        } else packages.set(name, mapped);
      }
    }
    assert.equal(packages.size, dependencies.size, "dependency map has unused packages");
    const packageFile = join(workspace, "packages.json");
    save(packageFile, { ...manifest, packages: [...packages.values()] });
    preservedMaps.push({ path: packageFile, before: fileIdentity(packageFile) });
    const guardLog = join(workspace, "git-rejections.log");
    writeFileSync(join(bin, "git"), `#!/usr/bin/env node\nimport(${JSON.stringify(new URL("./source-prepare-git.mjs", import.meta.url).href)});\n`, { mode: 0o700 });
    env.FIR_SOURCE_PREPARE_GIT_LOG = guardLog;
    const setups = [];
    for (const module of options.modules) {
      const output = invoke(lake, ["--keep-toolchain", "--no-cache", `--packages=${packageFile}`,
        "-KpostponeCompile=false", "query", "--json", `+${module}:setup`], project);
      const setup = JSON.parse(output);
      const path = join(workspace, `${module}.setup.json`);
      writeFileSync(path, output);
      setups.push({ module, path, ...fileIdentity(path), ...setupIdentities(setup, project, [workspace, toolchain]) });
    }
    assert(!existsSync(guardLog), "Git mutation/rematerialization attempted; see git-rejections.log");
    result = { workspace, project, tmp, toolchain: { directory: toolchain, leanCommit: options.leanCommit, version,
      lean: fileIdentity(lean), lake: fileIdentity(lake) },
      modules: options.modules, entries: options.entries ?? [],
      entryValidation: "selection only; declaration existence is checked by the downstream compiler",
      suppliedPaths: { path: resolve(options.packages), ...preservedMaps[0].before },
      packages: { path: packageFile, ...fileIdentity(packageFile) }, setups };
  } catch (error) { failure = error; }
  // Check both supplied sources and private originals, including new non-build files.
  for (const input of inputs) {
    try {
      assert.deepEqual(sourceIdentity(input.original), input.before, `supplied source mutated: ${input.original}`);
      assert.deepEqual(sourceIdentity(input.prepared), input.before, `private source mutated: ${input.prepared}`);
      assert(!existsSync(join(input.prepared, ".git")), "Git rematerialization detected");
    } catch (error) { failure = error; }
  }
  for (const map of preservedMaps) {
    try { assert.deepEqual(fileIdentity(map.path), map.before, `dependency path map mutated: ${map.path}`); }
    catch (error) { failure = error; }
  }
  if (failure) {
    writeFileSync(log, `\n${failure.stack}\n`, { flag: "a" });
    failure.message += `; full log: ${log}`;
    throw failure;
  }
  save(join(workspace, "PREPARED.json"), { ...result,
    sources: inputs.map(({ original, prepared, before }) => ({ original, prepared, files: before })) });
  return result;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const options = { modules: [], entries: [], verbose: false };
    const keys = { "--toolchain-dir": "toolchainDirectory", "--lean-commit": "leanCommit", "--source": "source", "--packages": "packages" };
    const args = process.argv.slice(2);
    for (let i = 0; i < args.length; i++) {
      const flag = args[i];
      if (flag === "--verbose") options.verbose = true;
      else {
        assert(args[i + 1] && !args[i + 1].startsWith("--"), `missing value: ${flag}`);
        const value = args[++i];
        if (flag === "--module") options.modules.push(value);
        else if (flag === "--entry") options.entries.push(value);
        else { assert(keys[flag], `unknown argument: ${flag}`); options[keys[flag]] = value; }
      }
    }
    for (const key of Object.values(keys)) assert(options[key], `missing required input: ${key}`);
    const result = prepareSource(options);
    console.log(`PASS source-prepare ${result.workspace}`);
  } catch (error) {
    console.error(`FAIL source-prepare: ${error.message}`);
    process.exitCode = error.exitCode ?? 1;
  }
}

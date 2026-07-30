import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import {
  appendFile,
  mkdir,
  readFile,
  stat,
  writeFile,
} from "node:fs/promises";
import {
  arch,
  cpus,
  hostname,
  platform,
  release,
  totalmem,
} from "node:os";
import { basename, dirname, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import {
  assessTiming,
  buildSchedule,
  expectedAggregate,
  summarizePhase,
} from "./benchmark-report.mjs";
import { expectedRuntimeChecksum } from "./reference.mjs";

function fail(message) {
  throw new Error(`benchmark.mjs: ${message}`);
}

function optionValue(args, index, option) {
  const value = args[index + 1];
  if (value === undefined) {
    fail(`${option} requires a value`);
  }
  return value;
}

function safeInteger(name, value, { minimum = 0, even = false } = {}) {
  if (!/^(0|[1-9][0-9]*)$/.test(value)) {
    fail(`${name} must be an unsigned decimal integer`);
  }
  const parsed = Number(value);
  if (
    !Number.isSafeInteger(parsed) ||
    parsed < minimum ||
    (even && parsed % 2 !== 0)
  ) {
    fail(
      `${name} must be ${even ? "an even " : ""}integer >= ${minimum}`,
    );
  }
  return parsed;
}

function uint64(name, value) {
  if (!/^(0|[1-9][0-9]*)$/.test(value)) {
    fail(`${name} must be an unsigned decimal integer`);
  }
  const parsed = BigInt(value);
  if (parsed >= 1n << 64n) {
    fail(`${name} does not fit in UInt64`);
  }
  return parsed;
}

const options = {
  artifacts: [],
  nativeGeneratedFlags: [],
  nativeHostFlags: [],
  nativeLinkFlags: [],
  warmups: 1,
  passes: 6,
  steadyRounds: 4096n,
  steadyIterations: 128,
  steadyWarmupIterations: 4,
  seed: 0x123456789abcdef0n,
};
const args = process.argv.slice(2);
for (let index = 0; index < args.length; index += 1) {
  const option = args[index];
  switch (option) {
    case "--manifest":
      options.manifest = optionValue(args, index, option);
      index += 1;
      break;
    case "--native":
      options.native = optionValue(args, index, option);
      index += 1;
      break;
    case "--out-dir":
      options.outDir = optionValue(args, index, option);
      index += 1;
      break;
    case "--artifact":
      options.artifacts.push(optionValue(args, index, option));
      index += 1;
      break;
    case "--native-generated-flag":
      options.nativeGeneratedFlags.push(optionValue(args, index, option));
      index += 1;
      break;
    case "--native-host-flag":
      options.nativeHostFlags.push(optionValue(args, index, option));
      index += 1;
      break;
    case "--native-link-flag":
      options.nativeLinkFlags.push(optionValue(args, index, option));
      index += 1;
      break;
    case "--warmups":
      options.warmups = safeInteger(
        "warmups",
        optionValue(args, index, option),
      );
      index += 1;
      break;
    case "--passes":
      options.passes = safeInteger(
        "passes",
        optionValue(args, index, option),
        { minimum: 2, even: true },
      );
      index += 1;
      break;
    case "--steady-rounds":
      options.steadyRounds = uint64(
        "steady rounds",
        optionValue(args, index, option),
      );
      index += 1;
      break;
    case "--steady-iterations":
      options.steadyIterations = safeInteger(
        "steady iterations",
        optionValue(args, index, option),
        { minimum: 1 },
      );
      index += 1;
      break;
    case "--steady-warmup-iterations":
      options.steadyWarmupIterations = safeInteger(
        "steady warmup iterations",
        optionValue(args, index, option),
      );
      index += 1;
      break;
    case "--seed":
      options.seed = uint64("seed", optionValue(args, index, option));
      index += 1;
      break;
    default:
      fail(`unknown option: ${option}`);
  }
}
for (const required of ["manifest", "native", "outDir"]) {
  if (options[required] === undefined) {
    fail(`missing --${required.replace(/[A-Z]/g, (letter) => `-${letter.toLowerCase()}`)}`);
  }
}
for (const [label, flags] of [
  ["generated compile", options.nativeGeneratedFlags],
  ["host compile", options.nativeHostFlags],
  ["link", options.nativeLinkFlags],
]) {
  if (flags.length === 0) {
    fail(`no native ${label} flags were recorded`);
  }
}

const laneDir = dirname(fileURLToPath(import.meta.url));
const workerPath = resolve(laneDir, "benchmark-emscripten.mjs");
const manifestPath = resolve(options.manifest);
const nativePath = resolve(options.native);
const outDir = resolve(options.outDir);
try {
  await stat(outDir);
  fail(`output directory already exists: ${outDir}`);
} catch (error) {
  if (error?.code !== "ENOENT") {
    throw error;
  }
}
await mkdir(outDir, { recursive: true });

const manifest = JSON.parse(await readFile(manifestPath, "utf8"));
if (
  manifest.profile !== "emscripten" ||
  manifest.runtime?.threads !== true ||
  !manifest.abi?.exports?.includes("fir_lcnf_c_runtime_checksum")
) {
  fail("manifest is not the required threaded RuntimeSmoke artifact");
}
const modulePath = resolve(dirname(manifestPath), manifest.artifacts.module.file);
const wasmPath = resolve(dirname(manifestPath), manifest.artifacts.wasm.file);

function hashBytes(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

async function fileIdentity(path) {
  const resolved = resolve(path);
  const [bytes, metadata] = await Promise.all([
    readFile(resolved),
    stat(resolved),
  ]);
  return {
    path: resolved,
    byteLength: metadata.size,
    sha256: hashBytes(bytes),
  };
}

async function execute(argv) {
  const start = process.hrtime.bigint();
  return await new Promise((resolvePromise, reject) => {
    const child = spawn(argv[0], argv.slice(1), {
      env: process.env,
      stdio: ["ignore", "pipe", "pipe"],
    });
    const stdout = [];
    const stderr = [];
    child.stdout.on("data", (chunk) => stdout.push(chunk));
    child.stderr.on("data", (chunk) => stderr.push(chunk));
    child.on("error", reject);
    child.on("close", (status, signal) => {
      const elapsedNs = process.hrtime.bigint() - start;
      resolvePromise({
        status,
        signal,
        elapsedNs,
        stdout: Buffer.concat(stdout).toString("utf8"),
        stderr: Buffer.concat(stderr).toString("utf8"),
      });
    });
  });
}

async function commandOutput(argv, label, { trim = true } = {}) {
  const result = await execute(argv);
  if (result.status !== 0 || result.signal !== null) {
    fail(
      `${label} failed with status ${result.status} signal ${result.signal}: ` +
        result.stderr,
    );
  }
  return trim ? result.stdout.trim() : result.stdout;
}

const repoRoot = await commandOutput(
  ["git", "-C", laneDir, "rev-parse", "--show-toplevel"],
  "git root discovery",
);
const [nativeLeancVersion, nativeHostCompilerVersion] = await Promise.all([
  commandOutput(
    ["lake", "-d", repoRoot, "env", "leanc", "--version"],
    "native leanc version",
  ),
  commandOutput(["cc", "--version"], "native host compiler version"),
]);

async function gitIdentity() {
  const [commit, status, diff] = await Promise.all([
    commandOutput(
      ["git", "-C", repoRoot, "rev-parse", "HEAD"],
      "git commit identity",
    ),
    commandOutput(
      ["git", "-C", repoRoot, "status", "--short"],
      "git status identity",
    ),
    commandOutput(
      ["git", "-C", repoRoot, "diff", "--binary", "--full-index", "HEAD"],
      "git diff identity",
      { trim: false },
    ),
  ]);
  return {
    commit,
    dirty: status !== "",
    status: status === "" ? [] : status.split("\n"),
    trackedDiffSha256: hashBytes(Buffer.from(diff)),
  };
}

const identityPaths = [
  manifestPath,
  modulePath,
  wasmPath,
  nativePath,
  workerPath,
  resolve(laneDir, "benchmark.mjs"),
  resolve(laneDir, "benchmark-report.mjs"),
  resolve(laneDir, "wasm-memory.mjs"),
  resolve(laneDir, "reference.mjs"),
  ...options.artifacts.map((path) => resolve(path)),
];
const uniqueIdentityPaths = [...new Set(identityPaths)].sort();

async function identitySnapshot() {
  return {
    git: await gitIdentity(),
    files: await Promise.all(uniqueIdentityPaths.map(fileIdentity)),
  };
}

function phaseArguments(phase) {
  if (phase === "startup") {
    return ["0", "1", "0", options.seed.toString()];
  }
  return [
    options.steadyRounds.toString(),
    String(options.steadyIterations),
    String(options.steadyWarmupIterations),
    options.seed.toString(),
  ];
}

function commandFor(profile, phase) {
  const phaseArgs = phaseArguments(phase);
  if (profile === "native") {
    return [nativePath, phase, ...phaseArgs];
  }
  return [
    process.execPath,
    workerPath,
    manifestPath,
    phase,
    ...phaseArgs,
  ];
}

function expectedResult(phase) {
  const rounds = phase === "startup" ? 0n : options.steadyRounds;
  const iterations = phase === "startup" ? 1 : options.steadyIterations;
  return expectedAggregate(
    expectedRuntimeChecksum(rounds, options.seed),
    iterations,
  );
}

async function runOne(profile, phase) {
  const command = commandFor(profile, phase);
  const result = await execute(command);
  if (result.status !== 0 || result.signal !== null) {
    fail(
      `${phase}/${profile} failed with status ${result.status} ` +
        `signal ${result.signal}: ${result.stderr}`,
    );
  }
  let child;
  try {
    child = JSON.parse(result.stdout);
  } catch (error) {
    fail(`${phase}/${profile} emitted invalid JSON: ${error}: ${result.stdout}`);
  }
  if (
    child.schemaVersion !== 1 ||
    child.profile !== profile ||
    child.phase !== phase
  ) {
    fail(`${phase}/${profile} emitted mismatched result metadata`);
  }
  const expected = expectedResult(phase);
  if (child.result !== expected.toString()) {
    fail(
      `${phase}/${profile} returned ${child.result}; expected ${expected}`,
    );
  }
  if (
    !/^[1-9][0-9]*$/.test(child.subjectElapsedNs) ||
    !/^[1-9][0-9]*$/.test(child.initializationElapsedNs)
  ) {
    fail(`${phase}/${profile} emitted invalid elapsed time`);
  }
  if (
    profile === "emscripten" &&
    child.runtime?.sharedMemory !== true
  ) {
    fail("threaded Emscripten artifact does not declare shared linear memory");
  }
  if (
    profile === "native" &&
    child.runtime?.processThreadCount !== null &&
    child.runtime?.processThreadCount < 1
  ) {
    child.runtime.processThreadCount = null;
  }
  return {
    command,
    processElapsedNs: result.elapsedNs.toString(),
    processStderr: result.stderr,
    child,
  };
}

const before = await identitySnapshot();
const warmupPath = resolve(outDir, "warmups.jsonl");
const rawPath = resolve(outDir, "raw-runs.jsonl");
const measuredRows = [];
const startedAt = new Date().toISOString();

for (const phase of ["startup", "steady"]) {
  for (let warmup = 0; warmup < options.warmups; warmup += 1) {
    const profiles =
      warmup % 2 === 0
        ? ["native", "emscripten"]
        : ["emscripten", "native"];
    for (let position = 0; position < profiles.length; position += 1) {
      const profile = profiles[position];
      const result = await runOne(profile, phase);
      await appendFile(
        warmupPath,
        `${JSON.stringify({
          kind: "warmup",
          phase,
          warmup,
          sequence: profiles.join("-"),
          position,
          profile,
          ...result,
        })}\n`,
      );
    }
  }

  for (const scheduled of buildSchedule(options.passes)) {
    const result = await runOne(scheduled.profile, phase);
    const row = {
      kind: "measured",
      phase,
      ...scheduled,
      ...result,
    };
    measuredRows.push(row);
    await appendFile(rawPath, `${JSON.stringify(row)}\n`);
  }
}

const after = await identitySnapshot();
const identityStable = JSON.stringify(before) === JSON.stringify(after);
await writeFile(
  resolve(outDir, "identity-check.json"),
  `${JSON.stringify({ stable: identityStable, before, after }, null, 2)}\n`,
);
if (!identityStable) {
  fail("binary, input, Git, or tracked-diff identity changed during the run");
}

const logicalElements =
  Number(options.steadyRounds) * options.steadyIterations;
if (!Number.isSafeInteger(logicalElements)) {
  fail("steady logical element count exceeds the safe integer range");
}
const startup = summarizePhase(measuredRows, "startup");
const steady = summarizePhase(measuredRows, "steady", logicalElements);
const identityByPath = new Map(
  before.files.map((record) => [record.path, record]),
);
const nativeArtifact = identityByPath.get(nativePath);
const manifestArtifact = identityByPath.get(manifestPath);
const moduleArtifact = identityByPath.get(modulePath);
const wasmArtifact = identityByPath.get(wasmPath);
const deploymentBytes =
  manifestArtifact.byteLength +
  moduleArtifact.byteLength +
  wasmArtifact.byteLength;
const declaredSharedMemory = measuredRows
  .filter((row) => row.profile === "emscripten")
  .every((row) => row.child.runtime.sharedMemory === true);
const configurationWarnings = [];
if (options.passes < 6) {
  configurationWarnings.push("fewer than six passes: screening evidence only");
}
if (options.warmups === 0) {
  configurationWarnings.push("no process warmups were run");
}
if (
  steady.native.subjectElapsedNs.median < 10_000_000 ||
  steady.emscripten.subjectElapsedNs.median < 10_000_000
) {
  configurationWarnings.push(
    "a median steady sample is shorter than 10 ms; increase the workload " +
      "before using timing as acceptance evidence",
  );
}
const timingAssessment = assessTiming({ startup, steady });
const warnings = [
  ...configurationWarnings,
  ...timingAssessment.warnings,
];
const timingStatus =
  timingAssessment.status === "inconclusive"
    ? "inconclusive"
    : configurationWarnings.length > 0
      ? "screening"
      : "baseline";

async function optionalText(path) {
  try {
    return (await readFile(path, "utf8")).trim();
  } catch (error) {
    if (error?.code === "ENOENT") {
      return null;
    }
    throw error;
  }
}

const report = {
  schemaVersion: 1,
  reportType: "lcnf-c-wasm-native-emscripten-performance",
  evidenceClassification: {
    deterministic: [
      "Git and tracked-diff identity",
      "input and artifact SHA-256 digests",
      "artifact byte lengths",
      "exact commands and workload endpoint",
      "Wasm shared-memory declaration and initial/maximum byte lengths",
    ],
    noisy: [
      "elapsed time",
      "throughput",
      "maximum resident set size",
      "observed host process thread count",
    ],
    semantic: [
      "every result matched the independent JavaScript oracle",
      "the manifest loader verified JavaScript and Wasm digests",
      "the Emscripten artifact declared shared linear memory",
    ],
  },
  startedAt,
  completedAt: new Date().toISOString(),
  host: {
    hostname: hostname(),
    platform: platform(),
    release: release(),
    architecture: arch(),
    logicalCpuCount: cpus().length,
    cpuModel: cpus()[0]?.model ?? null,
    totalMemoryBytes: totalmem(),
    cpuGovernor: await optionalText(
      "/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor",
    ),
    node: process.version,
  },
  environment: {
    NODE_OPTIONS: process.env.NODE_OPTIONS ?? null,
    UV_THREADPOOL_SIZE: process.env.UV_THREADPOOL_SIZE ?? null,
  },
  identity: before,
  toolchain: {
    ...manifest.toolchain,
    native: {
      leanc: nativeLeancVersion,
      hostCCompiler: nativeHostCompilerVersion,
    },
  },
  build: {
    native: {
      mode: "release",
      generatedCompileFlags: options.nativeGeneratedFlags,
      hostCompileFlags: options.nativeHostFlags,
      linkFlags: options.nativeLinkFlags,
    },
    emscripten: manifest.build,
    runtime: manifest.runtime,
  },
  workload: {
    class: "representative",
    function: "fir_lcnf_c_runtime_checksum",
    behavior:
      "array growth/fold, Std.HashMap insert/lookup, Except, closures, and String",
    seed: options.seed.toString(),
    startup: {
      rounds: "0",
      iterations: 1,
      subjectBoundary: {
        native: "Lean runtime and RuntimeSmoke module initialization",
        emscripten:
          "manifest read, digest verification, JS import, Wasm instantiation, " +
          "Lean runtime and RuntimeSmoke module initialization",
      },
      processBoundary: "host process spawn through clean exit",
    },
    steady: {
      roundsPerIteration: options.steadyRounds.toString(),
      measuredIterations: options.steadyIterations,
      inProcessWarmupIterations: options.steadyWarmupIterations,
      logicalElementsPerSample: logicalElements,
      subjectBoundary:
        "repeated initialized runtimeChecksum calls; process startup excluded",
    },
    processWarmupsPerPhaseAndProfile: options.warmups,
    passes: options.passes,
    order: "alternating native-emscripten / emscripten-native",
    expectedEndpoint: "exit status 0 and exact UInt64 oracle checksum",
  },
  commands: {
    startup: {
      native: commandFor("native", "startup"),
      emscripten: commandFor("emscripten", "startup"),
    },
    steady: {
      native: commandFor("native", "steady"),
      emscripten: commandFor("emscripten", "steady"),
    },
  },
  artifacts: {
    nativeExecutable: nativeArtifact,
    emscriptenDeployment: {
      manifest: manifestArtifact,
      module: moduleArtifact,
      wasm: wasmArtifact,
      totalByteLength: deploymentBytes,
      wasmVsNativeExecutableSizeRatio:
        wasmArtifact.byteLength / nativeArtifact.byteLength,
      deploymentVsNativeExecutableSizeRatio:
        deploymentBytes / nativeArtifact.byteLength,
    },
  },
  results: {
    startup,
    steady,
    timingAssessment: {
      ...timingAssessment,
      status: timingStatus,
      configurationWarnings,
    },
    threadedRuntimeEnvelope: {
      scope:
        "whole Node plus thread-enabled Emscripten host process; this does " +
        "not isolate pthread support from Node/JIT overhead",
      threadsRequiredByManifest: manifest.runtime.threads,
      sharedLinearMemoryDeclared: declaredSharedMemory,
      processThreadCountMedian: {
        native: steady.native.processThreadCount?.median ?? null,
        emscripten: steady.emscripten.processThreadCount?.median ?? null,
      },
      maxRssBytesMedian: {
        native: steady.native.maxRssBytes?.median ?? null,
        emscripten: steady.emscripten.maxRssBytes?.median ?? null,
      },
      declaredInitialWasmLinearMemoryBytes:
        steady.emscripten.declaredInitialLinearMemoryBytes?.median ?? null,
      declaredWasmMemory:
        measuredRows.find((row) => row.profile === "emscripten")
          ?.child.runtime.declaredMemory ?? null,
      coldProcessElapsedRatio:
        startup.comparison.processMedianRatio,
    },
  },
  rawEvidence: {
    warmups: basename(warmupPath),
    measuredRuns: basename(rawPath),
    identityCheck: "identity-check.json",
  },
  warnings,
  decision:
    timingStatus === "baseline"
      ? "Baseline/reporting evidence only; no optimization candidate is " +
        "accepted or rejected by this run."
      : `${timingStatus} timing evidence; use the preserved raw rows to ` +
        "adjust workload/repeats or control the host before making a " +
        "performance claim.",
  remainingHotspot:
    "Collect a sampled profile of the representative steady workload before " +
    "choosing an optimization target.",
};
const reportPath = resolve(outDir, "report.json");
await writeFile(reportPath, `${JSON.stringify(report, null, 2)}\n`);
const reportRelativePath = relative(repoRoot, reportPath);
const reportDisplayPath =
  reportRelativePath === ".." || reportRelativePath.startsWith("../")
    ? reportPath
    : reportRelativePath;

console.log(
  JSON.stringify(
    {
      report: reportDisplayPath,
      startupProcessMedianRatio: startup.comparison.processMedianRatio,
      steadySubjectMedianRatio: steady.comparison.subjectMedianRatio,
      nativeMedianLogicalElementsPerSecond:
        steady.native.logicalElementsPerSecond.median,
      emscriptenMedianLogicalElementsPerSecond:
        steady.emscripten.logicalElementsPerSecond.median,
      nativeExecutableBytes: nativeArtifact.byteLength,
      emscriptenDeploymentBytes: deploymentBytes,
      sharedLinearMemoryDeclared: declaredSharedMemory,
      identityStable,
      timingStatus,
      warnings,
    },
    null,
    2,
  ),
);

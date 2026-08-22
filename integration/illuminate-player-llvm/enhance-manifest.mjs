import { createHash } from "node:crypto";
import { readFile, stat, writeFile } from "node:fs/promises";
import path from "node:path";

function fail(message) {
  throw new Error(`enhance-manifest.mjs: ${message}`);
}

function sha256(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

const [manifestArgument, sourceContractArgument, firCommit, firDirty] = process.argv.slice(2);
if (!manifestArgument || !sourceContractArgument || !firCommit || firDirty === undefined) {
  fail("usage: enhance-manifest.mjs MANIFEST SOURCE-CONTRACT FIR-COMMIT FIR-DIRTY");
}

const manifestPath = path.resolve(manifestArgument);
const sourceContractPath = path.resolve(sourceContractArgument);
const [manifest, sourceContract] = await Promise.all([
  readFile(manifestPath, "utf8").then(JSON.parse),
  readFile(sourceContractPath, "utf8").then(JSON.parse),
]);

if (manifest.profile !== "emscripten") fail("base manifest profile is not Emscripten");
if (manifest.runtime?.threads !== false) fail("base manifest is not an unthreaded runtime");
if (manifest.build?.runtimeProfile !== "unthreaded") {
  fail("base manifest does not name the unthreaded runtime profile");
}

const packageRoot = path.dirname(manifestPath);
for (const [label, artifact] of Object.entries(manifest.artifacts ?? {})) {
  const artifactPath = path.join(packageRoot, artifact.file);
  const [bytes, metadata] = await Promise.all([readFile(artifactPath), stat(artifactPath)]);
  if (bytes.byteLength !== artifact.byteLength || sha256(bytes) !== artifact.sha256) {
    fail(`${label} artifact disagrees with the base manifest`);
  }
  if (metadata.size !== artifact.byteLength) fail(`${label} byte length is unstable`);
}

const generatedInputs = manifest.sources;
manifest.producer = {
  protocol: "browser-benchmarks/source-package/v1",
  adapter: "fir-llvm",
  runtimeBoundary: "browser-benchmarks/bounded-runtime/v1",
};
manifest.sources = {
  fir: {
    commit: firCommit,
    dirty: firDirty === "true",
  },
  illuminate: {
    repository: sourceContract.repository,
    commit: sourceContract.revision,
    dirty: false,
    relevantFiles: sourceContract.relevantFiles,
    sourceView: {
      mechanism: "Lake external source root with entry-context C specialization",
      modules: [
        "Illuminate.Animation.Types",
        "Illuminate.Animation.Player",
        "Illuminate.Animation.FirSelection",
      ],
      consumedCheckoutBuildArtifacts: false,
      generatedDependencyC: ["Types.c", "Player.c", "FirSelection.c"],
    },
  },
  generatedInputs,
};
manifest.entry = {
  initial: "Illuminate.AnimationPlayer.initialSelectionLive",
  transition: "Illuminate.AnimationPlayer.transitionSelectionLive",
  wireModule: "Fir.LlvmSelection",
  compiledExports: [
    "fir_illuminate_selection_create_wire",
    "fir_illuminate_selection_dispatch_wire",
    "fir_illuminate_selection_dispatch_tick",
  ],
};
manifest.capabilities = {
  browserAdapter: {
    apiVersion: "fir.illuminate-player.browser/v4",
    methods: ["createPlayer", "dispatch", "dispatchTick", "disposePlayer", "replayTrace"],
  },
  inputLayout: {
    version: "lean-4.32-Illuminate.Animation.SelectionAnimation/v4",
    projection: "fps, totalFrames, segment bounds, and steps only",
    excluded: ["segment.sync", "segment.pmap", "segment.params"],
  },
  ownership: {
    version: "fir.illuminate-player.persistent-checkpoint/v2",
    policy: "C table retains Lean animation/state until explicit idempotent disposal",
    applicationAddresses: "none",
    output: "copied JavaScript FrameSelection and scheduling Boolean",
  },
  hotEvent: {
    version: "fir.illuminate-player.hot-event/v1",
    method: "dispatchTick(player, timestamp)",
    transport: "direct Wasm f64",
  },
  emscriptenWire: {
    version: "fir.illuminate-player.emscripten-wire/v1",
    byteOrder: "little-endian",
    natural: "validated UInt32 transported into Lean Nat",
    timestamp: "IEEE-754 binary64 bits or direct Wasm f64",
  },
};
manifest.runtime = {
  ...manifest.runtime,
  threads: false,
  crossOriginIsolated: false,
  memoryOwner: "Emscripten module",
  playerReclamation: "explicit disposePlayer; module release is a package-internal fallback",
};
manifest.timings = {
  projectMs: "browser animation validation and SVG-free timeline projection",
  encodeMs: "wire encoding plus copy into Emscripten memory",
  executeMs: "only the exported C/Lean create or transition call",
  decodeMs: "copy response bytes and decode copied selection values",
  totalMs: "independent wall interval around the complete public operation",
  overheadMs: "total minus the non-overlapping named phase intervals",
};

await writeFile(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);

import {
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
  ILLUMINATE_SELECTION_PLAYER_RUNTIME_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";
import { BROWSER_PACKAGE_POLICY_VERSION } from
  "../package-tools/verified-package.mjs";

export const selectionPayloadFiles = Object.freeze([
  "BUILD.json",
  "illuminate-selection-player-browser-adapter.mjs",
  "illuminate-selection-player.wasm",
  "illuminate-selection-player.wasm.json",
  "smoke.mjs",
]);

export const selectionExpectedExports = Object.freeze([
  { name: "Illuminate.AnimationPlayer.initialSelectionLive", kind: "function" },
  { name: "Illuminate.AnimationPlayer.transitionSelectionLive", kind: "function" },
  { name: "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
    kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);

export const selectionPackagePolicy = Object.freeze({
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "Illuminate selection player v3",
  payloadFiles: selectionPayloadFiles,
  smokeFile: "smoke.mjs",
  build: {
    schemaVersion: "fir.illuminate-selection-player.build/v3",
    requiredValues: [
      { path: ["capabilities", "completeRuntime", "version"],
        equals: "fir.illuminate-player.complete-runtime/v2" },
      { path: ["capabilities", "completeRuntime", "selfContained"],
        equals: true },
      { path: ["capabilities", "completeRuntime", "residentRuntime", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_RUNTIME_VERSION },
      { path: ["capabilities", "completeRuntime", "residentRuntime", "provider"],
        equals: "none" },
      { path: ["capabilities", "completeRuntime", "residentRuntime",
        "externalDeclarations"], equals: [] },
      { path: ["capabilities", "browserAdapter", "apiVersion"],
        equals: ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION },
      { path: ["capabilities", "hotEvent", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION },
      { path: ["capabilities", "inputLayout", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION },
      { path: ["capabilities", "ownership", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION },
    ],
  },
  wasm: {
    file: "illuminate-selection-player.wasm",
    descriptorFile: "illuminate-selection-player.wasm.json",
    requireCompleteRuntime: true,
    requireZeroImports: true,
    memoryOwner: "module",
    expectedExports: selectionExpectedExports,
  },
  sourcePackage: {
    producer: {
      project: "fir",
      backend: "fir-native-wasm",
      lean: {
        toolchainPath: ["toolchain", "leanToolchain"],
        versionPath: ["toolchain", "leanVersion"],
      },
    },
    acceptance: { status: "accepted", authority: "verifier-policy" },
    evidenceFiles: ["illuminate-selection-player.wasm.json"],
    adapter: {
      file: "illuminate-selection-player-browser-adapter.mjs",
      apiVersionPath: ["capabilities", "browserAdapter", "apiVersion"],
      operationInventoryPath: ["capabilities", "browserAdapter", "methods"],
      startupFields: [],
      initializationFields: [],
    },
    operations: [
      { name: "createPlayer", mode: "production",
        inputContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#createPlayer/input`,
        resultContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#createPlayer/result`,
        phases: ["instantiateMs", "projectMs", "selectionEncodeMs",
          "stateSlotMs", "executeMs", "decodeMs", "rewindMs", "totalMs",
          "overheadMs"] },
      { name: "dispatch", mode: "diagnostic",
        inputContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#dispatch/input`,
        resultContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#dispatch/result`,
        phases: ["encodeMs", "executeMs", "decodeMs", "rewindMs", "totalMs",
          "overheadMs"] },
      { name: "dispatchTick", mode: "production",
        inputContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#dispatchTick/input`,
        resultContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#dispatchTick/result`,
        phases: [] },
      { name: "dispatchTickTimed", mode: "diagnostic",
        inputContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#dispatchTickTimed/input`,
        resultContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#dispatchTickTimed/result`,
        phases: ["encodeMs", "executeMs", "decodeMs", "rewindMs", "totalMs",
          "overheadMs"] },
      { name: "disposePlayer", mode: "production",
        inputContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#disposePlayer/input`,
        resultContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#disposePlayer/result`,
        phases: [] },
      { name: "replayTrace", mode: "diagnostic",
        inputContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#replayTrace/input`,
        resultContract:
          `${ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION}#replayTrace/result`,
        phases: ["creation", "dispatches", "totalMs"] },
    ],
    ownership: {
      capabilityPath: ["capabilities", "ownership"],
      model: "persistent-checkpoint-per-instance",
      arena: "persistent-prefix-with-rewound-scratch",
      reclamation: "drop-instance",
      rawAddressesExposed: false,
      transfer: {
        publicInput: "borrowed-immutable-javascript-values",
        encodedInput: "fresh-transferred-lean-graph",
        output: "decoded-javascript-copy",
      },
    },
  },
});

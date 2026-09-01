import { BROWSER_PACKAGE_POLICY_VERSION } from
  "../package-tools/verified-package.mjs";
import {
  LEAN_COMPONENT_RUNTIME_PROVIDER_API,
  VBP_VERSO_VIEWER_ADAPTER_API_VERSION,
  VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION,
  VBP_VERSO_VIEWER_MOUNT_ENTRY,
  VBP_VERSO_VIEWER_OWNERSHIP_VERSION,
  VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
} from "./vbp-verso-viewer-browser-adapter.mjs";

export const vbpVersoViewerPayloadFiles = Object.freeze([
  "BUILD.json",
  "runtime-inventory.json",
  "smoke.mjs",
  "vbp-verso-viewer-browser-adapter.mjs",
  "vbp-verso-viewer.wasm",
  "vbp-verso-viewer.wasm.json",
]);

export const vbpVersoViewerPackagePolicy = Object.freeze({
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "VBP FIR-native Verso preview widget",
  payloadFiles: vbpVersoViewerPayloadFiles,
  smokeFile: "smoke.mjs",
  build: {
    schemaVersion: "fir.vbp-verso-viewer.build/v1",
    requiredValues: [
      { path: ["abi", "version"], equals: 1 },
      { path: ["hostFrontier", "functionImportCount"], equals: 41 },
      { path: ["hostFrontier", "memoryImportCount"], equals: 0 },
      { path: ["residentRuntime", "residualRuntimeOperations"], equals: 0 },
      { path: ["capabilities", "provider", "apiVersion"],
        equals: LEAN_COMPONENT_RUNTIME_PROVIDER_API },
      { path: ["capabilities", "browserAdapter", "apiVersion"],
        equals: VBP_VERSO_VIEWER_ADAPTER_API_VERSION },
      { path: ["capabilities", "inputLayout", "version"],
        equals: VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION },
      { path: ["capabilities", "ownership", "version"],
        equals: VBP_VERSO_VIEWER_OWNERSHIP_VERSION },
    ],
  },
  wasm: {
    file: "vbp-verso-viewer.wasm",
    requireCompleteRuntime: false,
    requireZeroImports: false,
    memoryOwner: "module",
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
    acceptance: { status: "provisional", authority: "vbp/performance" },
    evidenceFiles: ["vbp-verso-viewer.wasm.json", "runtime-inventory.json"],
    adapter: {
      file: "vbp-verso-viewer-browser-adapter.mjs",
      apiVersionPath: ["capabilities", "browserAdapter", "apiVersion"],
      operationInventoryPath: ["capabilities", "browserAdapter", "operations"],
      startupFields: ["fetchMs", "compileMs", "instantiateMs", "totalMs",
        "overheadMs"],
      initializationFields: [],
    },
    operations: [{
      name: "mount",
      entry: VBP_VERSO_VIEWER_MOUNT_ENTRY,
      mode: "production",
      inputContract: `${VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION}#mount`,
      resultContract: `${VBP_VERSO_VIEWER_ADAPTER_API_VERSION}#Bool`,
      phases: ["encodeMs", "executeMs", "decodeMs", "totalMs", "overheadMs"],
    }, {
      name: "unmount",
      entry: VBP_VERSO_VIEWER_UNMOUNT_ENTRY,
      mode: "production",
      inputContract: `${VBP_VERSO_VIEWER_INPUT_LAYOUT_VERSION}#unmount`,
      resultContract: `${VBP_VERSO_VIEWER_ADAPTER_API_VERSION}#Bool`,
      phases: ["encodeMs", "executeMs", "decodeMs", "totalMs", "overheadMs"],
    }],
    ownership: {
      capabilityPath: ["capabilities", "ownership"],
      model: "stateful-instance-lifetime-arena",
      arena: "one-module-owned-monotonic-arena-per-open-provider-runtime",
      reclamation: "drop-instance-and-release-host-resources-on-dispose",
      rawAddressesExposed: false,
      transfer: {
        publicInput: "borrowed-selector-and-RpcJson-JavaScript-values",
        encodedInput: "fresh-transferred-Lean-graph",
        output: "copied-JavaScript-Boolean",
      },
    },
  },
});

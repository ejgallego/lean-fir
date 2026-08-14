import assert from "node:assert/strict";

import { residentHelperFamily } from "../runtime-classification.mjs";
import { inspectFunction } from "./function-index-lib.mjs";

const declarations = new Set([
  "module", "type", "func", "param", "result", "local", "import",
  "export", "memory", "table", "global", "elem", "data", "tag", "start",
  "then", "else", "mut",
]);

function instructionClass(opcode) {
  if (["call", "return_call"].includes(opcode)) return "direct-call";
  if (["call_indirect", "call_ref", "return_call_indirect",
    "return_call_ref"].includes(opcode)) return "indirect-call";
  if (opcode.endsWith(".load") || opcode.includes(".load")) {
    return "memory-load";
  }
  if (opcode.endsWith(".store") || opcode.includes(".store")) {
    return "memory-store";
  }
  if (opcode.startsWith("memory.")) return "memory-management";
  if (["block", "loop", "if", "br", "br_if", "br_table", "return",
    "unreachable", "try", "throw", "rethrow"].includes(
    opcode)) return "control-flow";
  if (opcode.startsWith("local.") || opcode.startsWith("global.")) {
    return "local-global";
  }
  if (opcode.endsWith(".const")) return "constant";
  if (/^(?:i32|i64|f32|f64|v128)\./.test(opcode)) return "numeric";
  if (opcode.startsWith("ref.") || opcode.startsWith("table.")) {
    return "reference-table";
  }
  return "other";
}

function sortedCounts(map) {
  return [...map].map(([name, count]) => ({ name, count }))
    .sort((left, right) => right.count - left.count ||
      left.name.localeCompare(right.name));
}

function withoutStringsAndComments(source) {
  let result = "";
  let index = 0;
  let blockDepth = 0;
  let lineComment = false;
  let string = false;
  while (index < source.length) {
    const current = source[index];
    const next = source[index + 1];
    if (lineComment) {
      if (current === "\n") {
        lineComment = false;
        result += "\n";
      } else {
        result += " ";
      }
      index += 1;
      continue;
    }
    if (blockDepth !== 0) {
      if (current === "(" && next === ";") {
        blockDepth += 1;
        result += "  ";
        index += 2;
      } else if (current === ";" && next === ")") {
        blockDepth -= 1;
        result += "  ";
        index += 2;
      } else {
        result += current === "\n" ? "\n" : " ";
        index += 1;
      }
      continue;
    }
    if (string) {
      if (current === "\\") {
        result += "  ";
        index += Math.min(2, source.length - index);
      } else {
        if (current === "\"") string = false;
        result += current === "\n" ? "\n" : " ";
        index += 1;
      }
      continue;
    }
    if (current === ";" && next === ";") {
      lineComment = true;
      result += "  ";
      index += 2;
    } else if (current === "(" && next === ";") {
      blockDepth = 1;
      result += "  ";
      index += 2;
    } else {
      if (current === "\"") string = true;
      result += current === "\"" ? " " : current;
      index += 1;
    }
  }
  assert.equal(blockDepth, 0, "unterminated WAT block comment");
  assert.equal(string, false, "unterminated WAT string");
  return result;
}

function regexpEscape(value) {
  return String(value).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

export function extractedFunctionWat(wat, optimizerName) {
  const lexical = withoutStringsAndComments(wat);
  const functionStart = new RegExp(
    `^\\(func\\s+\\$${regexpEscape(optimizerName)}(?:\\s|\\))`);
  let depth = 0;
  let start = null;
  let end = null;
  for (let index = 0; index < lexical.length; index += 1) {
    const character = lexical[index];
    if (character === "(") {
      if (depth === 1 && functionStart.test(lexical.slice(index))) {
        assert.equal(start, null,
          `extracted module defines function ${optimizerName} twice`);
        start = index;
      }
      depth += 1;
    } else if (character === ")") {
      assert(depth > 0, "unbalanced WAT closing parenthesis");
      depth -= 1;
      if (start !== null && end === null && depth === 1) {
        end = index + 1;
      }
    }
  }
  assert.equal(depth, 0, "unbalanced WAT opening parenthesis");
  if (start === null) {
    throw new Error(`extracted module does not define function ${optimizerName}`);
  }
  assert.notEqual(end, null,
    `extracted module does not close function ${optimizerName}`);
  return wat.slice(start, end);
}

export function instructionSummary(wat) {
  const opcodes = new Map();
  const classes = new Map();
  for (const match of withoutStringsAndComments(wat).matchAll(/\(([^\s()]+)/g)) {
    const opcode = match[1];
    if (declarations.has(opcode) || opcode.startsWith("$")) {
      continue;
    }
    opcodes.set(opcode, (opcodes.get(opcode) ?? 0) + 1);
    const class_ = instructionClass(opcode);
    classes.set(class_, (classes.get(class_) ?? 0) + 1);
  }
  return {
    instructionCount: [...opcodes.values()].reduce((sum, count) =>
      sum + count, 0),
    classes: sortedCounts(classes),
    opcodes: sortedCounts(opcodes),
  };
}

export function boundedDisassembly(wat, maxLines) {
  assert(Number.isSafeInteger(maxLines) && maxLines >= 8,
    "bounded disassembly requires at least eight lines");
  const lines = wat.trimEnd().split(/\r?\n/);
  if (lines.length <= maxLines) {
    return { lineCount: lines.length, omittedLines: 0, lines };
  }
  const headCount = Math.ceil((maxLines - 1) * 0.75);
  const tailCount = maxLines - headCount - 1;
  const omittedLines = lines.length - headCount - tailCount;
  return {
    lineCount: lines.length,
    omittedLines,
    lines: [
      ...lines.slice(0, headCount),
      `;; ... ${omittedLines} line(s) omitted ...`,
      ...lines.slice(-tailCount),
    ],
  };
}

function callee(sidecar, index) {
  const function_ = sidecar.functions[index];
  if (function_ === undefined) {
    return { index, name: null, origin: "unattributed", family: null };
  }
  return {
    index,
    name: function_.name,
    origin: function_.origin,
    family: function_.origin === "resident-helper" && function_.name !== null ?
      residentHelperFamily(function_.name) : null,
  };
}

function calleeByOptimizerName(sidecar, optimizerName) {
  const function_ = sidecar.functions.find((candidate) =>
    candidate.optimizerName === optimizerName);
  if (function_ === undefined) {
    return {
      index: null,
      optimizerName,
      name: null,
      origin: "unattributed",
      family: null,
    };
  }
  return callee(sidecar, function_.index);
}

function callFamily(target) {
  if (target.family !== null) return target.family;
  return target.origin;
}

export function directCallSummary(wat, sidecar) {
  const counts = new Map();
  for (const match of withoutStringsAndComments(wat).matchAll(
    /\((?:call|return_call)\s+\$([^\s()]+)(?=[\s)])/g)) {
    const optimizerName = match[1];
    counts.set(optimizerName, (counts.get(optimizerName) ?? 0) + 1);
  }
  const targets = [...counts].map(([optimizerName, callSites]) => ({
    ...calleeByOptimizerName(sidecar, optimizerName),
    callSites,
  })).sort((left, right) => right.callSites - left.callSites ||
    (left.index ?? Number.MAX_SAFE_INTEGER) -
      (right.index ?? Number.MAX_SAFE_INTEGER) ||
    (left.optimizerName ?? "").localeCompare(right.optimizerName ?? ""));
  const families = new Map();
  for (const target of targets) {
    const family = callFamily(target);
    families.set(family, (families.get(family) ?? 0) + target.callSites);
  }
  return {
    directCount: targets.reduce((sum, target) => sum + target.callSites, 0),
    byFamily: sortedCounts(families),
    targets,
  };
}

export function makeFunctionView(sidecar, selector, wat, maxLines) {
  const function_ = inspectFunction(sidecar, selector);
  assert.equal(function_.imported, false,
    `function ${function_.index} is imported and has no local body`);
  const functionWat = extractedFunctionWat(wat, function_.optimizerName);
  const instructions = instructionSummary(functionWat);
  const calls = directCallSummary(functionWat, sidecar);
  const directInstructions = instructions.classes.find(({ name }) =>
    name === "direct-call")?.count ?? 0;
  assert.equal(calls.directCount, directInstructions,
    "direct-call summary and instruction histogram disagree");
  return {
    schemaVersion: "fir.wasm.function-view/v1",
    artifact: sidecar.artifact,
    function: {
      index: function_.index,
      name: function_.name,
      optimizerName: function_.optimizerName,
      origin: function_.origin,
      compilerShape: function_.compilerShape,
      bodyBytes: function_.bodyBytes,
      exportedAs: function_.exportedAs,
      directCallees: function_.directCallees.map((index) =>
        callee(sidecar, index)),
      directCallers: function_.directCallers.map((index) =>
        callee(sidecar, index)),
      unresolvedCallTargets: function_.unresolvedCallTargets,
    },
    instructions,
    calls,
    disassembly: boundedDisassembly(functionWat, maxLines),
  };
}

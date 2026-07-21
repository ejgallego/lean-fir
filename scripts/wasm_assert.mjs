export class WasmAssertionError extends Error {
  constructor(message) {
    super(message);
    this.name = "WasmAssertionError";
  }
}

function fail(message) {
  throw new WasmAssertionError(message);
}

function ok(value, message = "expected value to be truthy") {
  if (!value) {
    fail(message);
  }
}

function equal(actual, expected, message) {
  if (actual !== expected) {
    fail(message ?? `expected ${String(actual)} === ${String(expected)}`);
  }
}

function notEqual(actual, expected, message) {
  if (actual === expected) {
    fail(message ?? `expected ${String(actual)} !== ${String(expected)}`);
  }
}

function deepEqual(actual, expected) {
  if (Object.is(actual, expected)) {
    return true;
  }
  if (typeof actual !== typeof expected || actual === null || expected === null) {
    return false;
  }
  if (typeof actual !== "object") {
    return false;
  }
  if (Array.isArray(actual) || Array.isArray(expected)) {
    return Array.isArray(actual) && Array.isArray(expected) &&
      actual.length === expected.length &&
      actual.every((value, index) => deepEqual(value, expected[index]));
  }
  if (ArrayBuffer.isView(actual) || ArrayBuffer.isView(expected)) {
    return ArrayBuffer.isView(actual) && ArrayBuffer.isView(expected) &&
      actual.constructor === expected.constructor &&
      actual.length === expected.length &&
      actual.every((value, index) => Object.is(value, expected[index]));
  }
  const actualKeys = Object.keys(actual).sort();
  const expectedKeys = Object.keys(expected).sort();
  return deepEqual(actualKeys, expectedKeys) &&
    actualKeys.every((key) => deepEqual(actual[key], expected[key]));
}

function printable(value) {
  try {
    return JSON.stringify(value, (_key, item) =>
      typeof item === "bigint" ? `${item}n` : item);
  } catch {
    return String(value);
  }
}

function deepStrictEqual(actual, expected, message) {
  if (!deepEqual(actual, expected)) {
    fail(message ?? `expected ${printable(actual)} to deeply equal ${printable(expected)}`);
  }
}

export default Object.freeze({ ok, equal, notEqual, deepStrictEqual });

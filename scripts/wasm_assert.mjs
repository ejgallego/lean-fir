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

export default Object.freeze({ ok, equal, notEqual });

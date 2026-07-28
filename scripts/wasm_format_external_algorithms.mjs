import assert from "./wasm_assert.mjs";

const encoder = new TextEncoder();
const decoder = new TextDecoder();

function utf8Width(first) {
  if (first < 0x80) return 1;
  if (first >= 0xc0 && first < 0xe0) return 2;
  if (first >= 0xe0 && first < 0xf0) return 3;
  if (first >= 0xf0 && first < 0xf8) return 4;
  return 1;
}

export function stringAppend(left, right) {
  return left + right;
}

export function stringPushn(source, codePoint, count) {
  assert.ok(count <= BigInt(Number.MAX_SAFE_INTEGER),
    "String.Internal.pushn count is too large");
  return source + String.fromCodePoint(Number(codePoint)).repeat(Number(count));
}

export function stringCompare(left, right) {
  const leftBytes = encoder.encode(left);
  const rightBytes = encoder.encode(right);
  const commonLength = Math.min(leftBytes.length, rightBytes.length);
  for (let index = 0; index < commonLength; ++index) {
    if (leftBytes[index] < rightBytes[index]) return 0n;
    if (leftBytes[index] > rightBytes[index]) return 2n;
  }
  if (leftBytes.length < rightBytes.length) return 0n;
  if (leftBytes.length > rightBytes.length) return 2n;
  return 1n;
}

export function stringLength(source) {
  return BigInt(Array.from(source).length);
}

export function stringPosOf(source, codePoint) {
  const bytes = encoder.encode(source);
  const needle = encoder.encode(String.fromCodePoint(Number(codePoint)));
  let offset = bytes.length;
  search: for (let index = 0; index + needle.length <= bytes.length; ++index) {
    for (let part = 0; part < needle.length; ++part) {
      if (bytes[index + part] !== needle[part]) continue search;
    }
    offset = index;
    break;
  }
  return BigInt(offset);
}

export function stringOffsetOfPos(source, position) {
  const bytes = encoder.encode(source);
  const end = Math.min(Number(position), bytes.length);
  return BigInt(Array.from(decoder.decode(bytes.slice(0, end))).length);
}

export function stringUtf8ByteSize(source) {
  return BigInt(encoder.encode(source).length);
}

export function stringExtract(source, begin, end) {
  if (begin >= end) return "";
  let position = 0n;
  let result = "";
  let foundBegin = false;
  for (const char of source) {
    if (!foundBegin) {
      if (position === begin) {
        foundBegin = true;
      } else {
        position += BigInt(encoder.encode(char).length);
        continue;
      }
    }
    if (position === end) return result;
    result += char;
    position += BigInt(encoder.encode(char).length);
  }
  return foundBegin ? result : "";
}

export function stringNext(source, position) {
  const bytes = encoder.encode(source);
  const index = Number(position);
  return BigInt(index < bytes.length ? index + utf8Width(bytes[index]) : index + 1);
}

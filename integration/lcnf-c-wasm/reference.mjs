export const mask = (1n << 64n) - 1n;

const multiplier = 6364136223846793005n;
const increment = 1442695040888963407n;

export function asUInt64(value) {
  return value & mask;
}

function composeAffine(lhs, rhs) {
  return {
    multiplier: (lhs.multiplier * rhs.multiplier) & mask,
    increment:
      (lhs.multiplier * rhs.increment + lhs.increment) & mask,
  };
}

export function expectedMix(rounds, seed) {
  let accumulated = { multiplier: 1n, increment: 0n };
  let power = { multiplier, increment };
  let remaining = rounds;

  while (remaining !== 0n) {
    if ((remaining & 1n) !== 0n) {
      accumulated = composeAffine(power, accumulated);
    }
    power = composeAffine(power, power);
    remaining >>= 1n;
  }

  return (
    accumulated.multiplier * seed + accumulated.increment
  ) & mask;
}

function composeHeap(lhs, rhs) {
  return {
    multiplier: (lhs.multiplier * rhs.multiplier) & mask,
    increment:
      (lhs.multiplier * rhs.increment + lhs.increment) & mask,
    sumMultiplier:
      (rhs.sumMultiplier + lhs.sumMultiplier * rhs.multiplier) & mask,
    sumIncrement:
      (
        rhs.sumIncrement +
        lhs.sumMultiplier * rhs.increment +
        lhs.sumIncrement
      ) & mask,
  };
}

export function expectedHeapChecksum(rounds, seed) {
  let accumulated = {
    multiplier: 1n,
    increment: 0n,
    sumMultiplier: 0n,
    sumIncrement: 0n,
  };
  let power = {
    multiplier,
    increment,
    sumMultiplier: 1n,
    sumIncrement: 0n,
  };
  let remaining = rounds;

  while (remaining !== 0n) {
    if ((remaining & 1n) !== 0n) {
      accumulated = composeHeap(power, accumulated);
    }
    power = composeHeap(power, power);
    remaining >>= 1n;
  }

  return (
    accumulated.sumMultiplier * seed + accumulated.sumIncrement
  ) & mask;
}

export function expectedWasiCoreChecksum(rounds, seed) {
  const arraySum = expectedHeapChecksum(rounds, seed);
  const closureValue = ((arraySum + seed) & mask) ^ rounds;
  const labelByteLength = rounds === 0n ? 11n : 14n;
  return (closureValue + labelByteLength) & mask;
}

export function expectedWasiScalarChecksum(rounds, seed) {
  let remaining = rounds;
  let state = seed;
  let byteSum = 0n;

  while (remaining !== 0n) {
    byteSum = (byteSum + (state & 0xffn)) & mask;
    state = (state * multiplier + increment) & mask;
    remaining -= 1n;
  }

  const first = (byteSum + rounds + seed) & mask;
  return ((first ^ rounds) + seed) & mask;
}

export function expectedRuntimeChecksum(rounds, seed) {
  let remaining = rounds;
  let next = seed;
  let arraySum = 0n;
  let first;

  while (remaining !== 0n) {
    next = (next * multiplier + increment) & mask;
    const value = (
      next ^ ((remaining * 11400714819323198485n) & mask)
    ) & mask;
    if (first === undefined) {
      first = value;
    }
    arraySum = (arraySum + value) & mask;
    remaining -= 1n;
  }

  const missingLength = 9n;
  const firstOrMissing = first ?? missingLength;
  const label = `fir:${rounds}:${rounds}:${rounds}`;
  const labelLength = BigInt(new TextEncoder().encode(label).byteLength);
  const closureValue = ((arraySum + seed) & mask) ^ rounds;

  return (
    closureValue + firstOrMissing + missingLength + labelLength
  ) & mask;
}

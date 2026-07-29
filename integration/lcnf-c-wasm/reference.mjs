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

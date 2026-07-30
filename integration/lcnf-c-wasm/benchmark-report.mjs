const uint64Modulus = 1n << 64n;

function requireFinite(values, label) {
  if (values.length === 0 || values.some((value) => !Number.isFinite(value))) {
    throw new Error(`benchmark report: ${label} has no finite samples`);
  }
}

export function median(values) {
  requireFinite(values, "median");
  const sorted = [...values].sort((left, right) => left - right);
  const middle = Math.floor(sorted.length / 2);
  if (sorted.length % 2 === 1) {
    return sorted[middle];
  }
  return (sorted[middle - 1] + sorted[middle]) / 2;
}

export function distribution(values) {
  requireFinite(values, "distribution");
  const center = median(values);
  return {
    count: values.length,
    min: Math.min(...values),
    median: center,
    max: Math.max(...values),
    mean: values.reduce((sum, value) => sum + value, 0) / values.length,
    medianAbsoluteDeviation: median(
      values.map((value) => Math.abs(value - center)),
    ),
  };
}

export function buildSchedule(passes) {
  if (!Number.isSafeInteger(passes) || passes < 2 || passes % 2 !== 0) {
    throw new Error("benchmark report: passes must be an even integer >= 2");
  }
  const rows = [];
  for (let pass = 0; pass < passes; pass += 1) {
    const profiles =
      pass % 2 === 0
        ? ["native", "emscripten"]
        : ["emscripten", "native"];
    for (let position = 0; position < profiles.length; position += 1) {
      rows.push({
        pass,
        sequence: profiles.join("-"),
        position,
        profile: profiles[position],
      });
    }
  }
  return rows;
}

export function expectedAggregate(checksum, iterations) {
  const count = BigInt(iterations);
  return (
    (checksum * count + (count * (count - 1n)) / 2n) %
    uint64Modulus
  );
}

function numericField(rows, selector) {
  return rows
    .map(selector)
    .filter((value) => typeof value === "number" && Number.isFinite(value));
}

function profileSummary(rows, phase, profile, logicalElements) {
  const selected = rows.filter(
    (row) => row.phase === phase && row.profile === profile,
  );
  if (selected.length === 0) {
    throw new Error(`benchmark report: ${phase}/${profile} has no rows`);
  }
  const subjectElapsedNs = selected.map((row) =>
    Number(row.child.subjectElapsedNs),
  );
  const processElapsedNs = selected.map((row) =>
    Number(row.processElapsedNs),
  );
  const summary = {
    samples: selected.length,
    subjectElapsedNs: distribution(subjectElapsedNs),
    processElapsedNs: distribution(processElapsedNs),
  };
  const maxRssBytes = numericField(
    selected,
    (row) => row.child.runtime.maxRssBytes,
  );
  const processThreadCount = numericField(
    selected,
    (row) => row.child.runtime.processThreadCount,
  );
  const initialLinearMemoryBytes = numericField(
    selected,
    (row) => row.child.runtime.declaredMemory?.initialByteLength,
  );
  if (maxRssBytes.length > 0) {
    summary.maxRssBytes = distribution(maxRssBytes);
  }
  if (processThreadCount.length > 0) {
    summary.processThreadCount = distribution(processThreadCount);
  }
  if (initialLinearMemoryBytes.length > 0) {
    summary.declaredInitialLinearMemoryBytes = distribution(
      initialLinearMemoryBytes,
    );
  }
  if (logicalElements !== null) {
    summary.logicalElementsPerSecond = distribution(
      subjectElapsedNs.map(
        (elapsedNs) => logicalElements / (elapsedNs / 1_000_000_000),
      ),
    );
  }
  return summary;
}

function pairedRatios(rows, phase, field) {
  const byPass = new Map();
  for (const row of rows.filter((candidate) => candidate.phase === phase)) {
    let pair = byPass.get(row.pass);
    if (pair === undefined) {
      pair = {};
      byPass.set(row.pass, pair);
    }
    pair[row.profile] = Number(field(row));
  }
  const ratios = [];
  for (const [pass, pair] of byPass) {
    if (
      !Number.isFinite(pair.native) ||
      !Number.isFinite(pair.emscripten) ||
      pair.native <= 0
    ) {
      throw new Error(`benchmark report: phase ${phase} pass ${pass} is unpaired`);
    }
    ratios.push(pair.emscripten / pair.native);
  }
  return distribution(ratios);
}

function orderEffect(rows, phase, profile) {
  const selected = rows.filter(
    (row) => row.phase === phase && row.profile === profile,
  );
  const first = selected
    .filter((row) => row.position === 0)
    .map((row) => Number(row.child.subjectElapsedNs));
  const second = selected
    .filter((row) => row.position === 1)
    .map((row) => Number(row.child.subjectElapsedNs));
  const firstMedian = median(first);
  const secondMedian = median(second);
  return {
    firstMedianNs: firstMedian,
    secondMedianNs: secondMedian,
    secondVsFirstPercent: ((secondMedian - firstMedian) / firstMedian) * 100,
  };
}

export function summarizePhase(rows, phase, logicalElements = null) {
  const native = profileSummary(rows, phase, "native", logicalElements);
  const emscripten = profileSummary(
    rows,
    phase,
    "emscripten",
    logicalElements,
  );
  return {
    native,
    emscripten,
    comparison: {
      subjectMedianRatio:
        emscripten.subjectElapsedNs.median / native.subjectElapsedNs.median,
      processMedianRatio:
        emscripten.processElapsedNs.median / native.processElapsedNs.median,
      pairedSubjectRatios: pairedRatios(
        rows,
        phase,
        (row) => row.child.subjectElapsedNs,
      ),
      orderEffect: {
        native: orderEffect(rows, phase, "native"),
        emscripten: orderEffect(rows, phase, "emscripten"),
      },
    },
  };
}

export function assessTiming(
  summaries,
  {
    maximumRelativeMedianAbsoluteDeviationPercent = 10,
    maximumAbsoluteOrderEffectPercent = 10,
  } = {},
) {
  const warnings = [];
  for (const [phase, summary] of Object.entries(summaries)) {
    for (const profile of ["native", "emscripten"]) {
      const distribution = summary[profile].subjectElapsedNs;
      const relativeMadPercent =
        (distribution.medianAbsoluteDeviation / distribution.median) * 100;
      if (relativeMadPercent >= maximumRelativeMedianAbsoluteDeviationPercent) {
        warnings.push(
          `${phase}/${profile} subject timing has ` +
            `${relativeMadPercent.toFixed(2)}% relative median absolute deviation`,
        );
      }
      const orderPercent =
        summary.comparison.orderEffect[profile].secondVsFirstPercent;
      if (Math.abs(orderPercent) >= maximumAbsoluteOrderEffectPercent) {
        warnings.push(
          `${phase}/${profile} subject timing has ` +
            `${orderPercent.toFixed(2)}% second-vs-first order effect`,
        );
      }
    }
    const paired = summary.comparison.pairedSubjectRatios;
    const pairedRelativeMadPercent =
      (paired.medianAbsoluteDeviation / paired.median) * 100;
    if (
      pairedRelativeMadPercent >= maximumRelativeMedianAbsoluteDeviationPercent
    ) {
      warnings.push(
        `${phase} paired ratios have ` +
          `${pairedRelativeMadPercent.toFixed(2)}% relative median absolute deviation`,
      );
    }
  }
  return {
    status: warnings.length === 0 ? "baseline" : "inconclusive",
    thresholds: {
      maximumRelativeMedianAbsoluteDeviationPercent,
      maximumAbsoluteOrderEffectPercent,
    },
    warnings,
  };
}

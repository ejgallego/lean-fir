#!/usr/bin/env python3
"""Focused tests for bounded, canonically ordered validation work."""

from __future__ import annotations

import os
import threading
import time
import unittest
from unittest import mock

import validation_harness as validation


class ValidationParallelTests(unittest.TestCase):
    def test_job_count_is_explicitly_bounded(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=True):
            self.assertEqual(validation.validation_job_count(), 1)
        for value in ("0", "65", "-1", "1.5", "eight", ""):
            with self.assertRaisesRegex(
                validation.ValidationError, "FIR_CHECK_JOBS"
            ):
                validation.validation_job_count(value)
        self.assertEqual(validation.validation_job_count("8"), 8)

    def test_parallel_map_retains_input_order_and_bound(self) -> None:
        lock = threading.Lock()
        active = 0
        peak = 0

        def work(value: int) -> int:
            nonlocal active, peak
            with lock:
                active += 1
                peak = max(peak, active)
            time.sleep(0.01 * (4 - value))
            with lock:
                active -= 1
            return value * 10

        self.assertEqual(
            validation.ordered_parallel_map(work, [1, 2, 3], jobs=2),
            [10, 20, 30],
        )
        self.assertEqual(peak, 2)

    def test_worker_failure_propagates_before_publication(self) -> None:
        published = False

        def work(value: int) -> int:
            if value == 2:
                raise RuntimeError("worker failed")
            return value

        with self.assertRaisesRegex(RuntimeError, "worker failed"):
            results = validation.ordered_parallel_map(work, [1, 2, 3], jobs=2)
            published = bool(results)
        self.assertFalse(published)


if __name__ == "__main__":
    unittest.main()

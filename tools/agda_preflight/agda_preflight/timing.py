from __future__ import annotations

from collections import defaultdict
from contextlib import contextmanager
from dataclasses import dataclass
import time
from typing import Dict, Iterator


@dataclass(frozen=True)
class TimingSnapshot:
    stages_ns: Dict[str, int]
    counts: Dict[str, int]

    @property
    def total_ns(self) -> int:
        return self.stages_ns.get("request.total", 0)

    def as_dict(self) -> dict:
        return {
            "stages_ms": {
                name: round(value / 1_000_000.0, 3)
                for name, value in sorted(self.stages_ns.items())
            },
            "counts": dict(sorted(self.counts.items())),
        }


class Profiler:
    """Small request-local profiler for the interactive preflight path.

    Stage durations are cumulative: entering the same stage multiple times adds
    to the existing total. Counts are explicit so performance regressions can
    distinguish, for example, a slower parser from accidentally parsing 500
    clean modules.
    """

    def __init__(self) -> None:
        self._stages_ns = defaultdict(int)
        self._counts = defaultdict(int)

    @contextmanager
    def stage(self, name: str) -> Iterator[None]:
        start = time.perf_counter_ns()
        try:
            yield
        finally:
            self._stages_ns[name] += time.perf_counter_ns() - start

    def add_ns(self, name: str, value: int) -> None:
        self._stages_ns[name] += max(0, int(value))

    def count(self, name: str, value: int = 1) -> None:
        self._counts[name] += int(value)

    def snapshot(self) -> TimingSnapshot:
        return TimingSnapshot(dict(self._stages_ns), dict(self._counts))

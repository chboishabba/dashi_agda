from __future__ import annotations

from pathlib import Path
import sys

import numpy as np


SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_triad_transfer_rank_capture_curve import (  # noqa: E402
    RECORD_DTYPE,
    _records_for_chunk,
    capture_summary,
    retain_top_records,
)


def _chunk(values: list[float], k: tuple[int, int, int], start: int) -> np.ndarray:
    p = np.asarray([(start + index, 1, 0) for index in range(len(values))], dtype=np.int64)
    q = np.asarray([(k[0] - row[0], k[1] - row[1], k[2] - row[2]) for row in p], dtype=np.int64)
    return _records_for_chunk(np.asarray(values, dtype=np.float64), np.asarray(k), p, q)


def test_retain_top_records_is_exact_across_chunks() -> None:
    retained = np.empty(0, dtype=RECORD_DTYPE)
    retained = retain_top_records(retained, _chunk([1.0, 4.0, 2.0], (8, 1, 0), 1), 2)
    retained = retain_top_records(retained, _chunk([3.0, 5.0], (9, 1, 0), 5), 2)
    assert sorted((float(value) for value in retained["value"]), reverse=True) == [5.0, 4.0]


def test_capture_summary_reports_exact_and_lower_bound_targets() -> None:
    retained = np.empty(0, dtype=RECORD_DTYPE)
    retained = retain_top_records(retained, _chunk([1.0, 4.0, 2.0], (8, 1, 0), 1), 2)
    retained = retain_top_records(retained, _chunk([3.0, 5.0], (9, 1, 0), 5), 2)

    summary = capture_summary(
        retained,
        full_gross=10.0,
        total_atom_count=5,
        rank_counts=(1, 2),
        capture_targets=(0.5, 0.9, 0.95),
    )
    curve = summary["rank_curve"]
    assert curve[0]["rank"] == 1
    assert curve[0]["gross_activity_fraction"] == 0.5
    assert curve[1]["rank"] == 2
    assert curve[1]["gross_activity_fraction"] == 0.9
    assert curve[1]["reality_closed_mode_count"] >= curve[0]["reality_closed_mode_count"]

    targets = {row["target_fraction"]: row for row in summary["capture_target_rank_bounds"]}
    assert targets[0.5]["exact_atom_rank"] == 1
    assert targets[0.9]["exact_atom_rank"] == 2
    assert targets[0.95]["reached_within_retained_prefix"] is False
    assert targets[0.95]["atom_rank_lower_bound"] == 3

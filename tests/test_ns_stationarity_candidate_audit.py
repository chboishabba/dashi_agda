from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_stationarity_candidate_audit.py"
STEM = "ns_stationarity_candidate_audit"
REQUIRED_IDS = ("A1.1", "A1.2", "A1.3", "A3.1", "A3.2", "A3.3", "A3.4")

PROMOTED_TRUE_PATTERNS = (
    re.compile(r'"(?:promoted|promotion_allowed|clay[^"]*promoted|proved)"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\b(?:promoted|promotion_allowed|stationarity_proved|clay[_\s-]*navier[_\s-]*stokes[_\s-]*promoted)\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_audit(tmp_path: Path, *extra: str) -> tuple[dict[str, Any], list[dict[str, Any]], str]:
    out_dir = tmp_path / STEM
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
            *extra,
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    artifact_text = ""
    if out_dir.exists():
        artifact_text = "\n".join(
            path.read_text(encoding="utf-8", errors="replace")
            for path in sorted(out_dir.glob("*"))
            if path.suffix.lower() in {".json", ".csv", ".md"}
        )
    text = "\n".join([result.stdout, result.stderr, artifact_text])
    assert result.returncode == 0, text
    summary = json.loads((out_dir / f"{STEM}_summary.json").read_text(encoding="utf-8"))
    rows = json.loads((out_dir / f"{STEM}_rows.json").read_text(encoding="utf-8"))
    assert isinstance(summary, dict)
    assert isinstance(rows, list)
    return summary, rows, text


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def bool_values_for_key_terms(value: Any, *terms: str) -> list[bool]:
    found: list[bool] = []
    lowered_terms = tuple(term.lower() for term in terms)
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        for key, child in item.items():
            if isinstance(child, bool) and any(term in str(key).lower() for term in lowered_terms):
                found.append(child)
    return found


def bool_values_for_exact_keys(value: Any, *keys: str) -> list[bool]:
    found: list[bool] = []
    wanted = {key.lower() for key in keys}
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        for key, child in item.items():
            if isinstance(child, bool) and str(key).lower() in wanted:
                found.append(child)
    return found


def test_stationarity_candidate_writes_json_csv_markdown_and_required_ids(tmp_path: Path) -> None:
    summary, rows, text = run_audit(tmp_path)

    assert summary["contract"] == STEM
    assert summary["status"] == "candidate_non_promoting_fail_closed"
    assert tuple(summary["required_theorem_ids"]) == REQUIRED_IDS
    assert tuple(summary["present_theorem_ids"]) == REQUIRED_IDS
    assert [row["theorem_id"] for row in rows] == list(REQUIRED_IDS)
    assert summary["checks"]["required_theorem_ids_present"] is True
    assert summary["checks"]["required_theorem_ids_exact"] is True
    assert "A1.1-A3.4" in text
    assert "Gaussian weighted W_r" in text or "gaussian_weighted_W_r" in text


def test_stationarity_candidate_records_alpha_delta_and_abel_q_choice(tmp_path: Path) -> None:
    summary, rows, text = run_audit(tmp_path)
    payload = {"summary": summary, "rows": rows}

    assert summary["pressure_tail_alpha"]["fraction"] == "1/6"
    assert summary["pressure_tail_alpha"]["value"] == 1 / 6
    assert summary["delta_r_candidate"]["formula"] == "O(r^min(1/4, alpha))"
    assert summary["delta_r_candidate"]["min_exponent_fraction"] == "1/6"
    assert summary["delta_r_candidate"]["for_alpha_one_sixth"] == "O(r^1/6)"
    assert summary["abel_summation"]["q"] == 7
    assert summary["abel_summation"]["q_times_beta_fraction"] == "7/6"
    assert summary["abel_summation"]["numeric_check_passes"] is True
    assert summary["abel_summation"]["closure_proved"] is False
    assert "pressure-tail" in text
    assert "delta_r" in text
    assert "Abel" in text
    assert any(row["route_component"] == "energy_ode_route" for row in rows)
    assert any(row["route_component"] == "delta_r_candidate_rate" for row in rows)
    assert any(row["route_component"] == "abel_summation_q_candidate" for row in rows)
    assert bool_values_for_key_terms(payload, "closure_proved") == [False]


def test_stationarity_candidate_never_reports_proved_or_promoted(tmp_path: Path) -> None:
    summary, rows, text = run_audit(tmp_path)
    payload = {"summary": summary, "rows": rows}

    proved_values = bool_values_for_exact_keys(payload, "proved", "stationarity_proved")
    promoted_values = bool_values_for_exact_keys(
        payload,
        "promoted",
        "promotion_allowed",
        "clay_promoted",
        "clay_navier_stokes_promoted",
    )
    assert proved_values and all(value is False for value in proved_values), proved_values
    assert promoted_values and all(value is False for value in promoted_values), promoted_values
    assert summary["promotion_status"]["candidate_only"] is True
    assert summary["promotion_status"]["stationarity_proved"] is False
    assert summary["promotion_status"]["clay_navier_stokes_promoted"] is False
    assert all(row["candidate_status"].endswith(("not_proved", "not_proved")) or "not_proved" in row["candidate_status"] for row in rows)
    for pattern in PROMOTED_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_stationarity_candidate_markdown_stdout_is_available(tmp_path: Path) -> None:
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--format",
            "md",
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.startswith("# NS Stationarity Candidate Audit")
    assert "candidate_non_promoting_fail_closed" in result.stdout
    assert "A3.4" in result.stdout


def test_stationarity_candidate_source_contains_no_positive_promotion_assignment() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    for pattern in PROMOTED_TRUE_PATTERNS:
        assert not pattern.search(source), pattern.pattern

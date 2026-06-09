from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint115_flux_budget_scaling.py"
OUT_STEM = "ns_sprint115_flux_budget_scaling"

DELTAS = (0.10, 0.20, 0.30, 0.40, 0.48)
REYNOLDS = (1.0e3, 1.0e4, 1.0e5)


def run_scaling(tmp_path: Path) -> tuple[dict[str, Any], list[dict[str, Any]], str]:
    assert SCRIPT.exists(), "Sprint115 flux budget scaling script is missing"

    out_dir = tmp_path / OUT_STEM
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 1, result.stdout + result.stderr

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "script did not write JSON output"
    assert csv_paths, "script did not write CSV output"
    assert md_paths, "script did not write Markdown output"

    summary_path = next((path for path in json_paths if "summary" in path.name), json_paths[0])
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    rows = collect_rows(summary, json_paths, csv_paths)
    assert rows, "script did not emit any grid rows"

    output_text = "\n".join(
        [
            result.stdout,
            result.stderr,
            json.dumps(summary, sort_keys=True),
            *[path.read_text(encoding="utf-8") for path in json_paths],
            *[path.read_text(encoding="utf-8") for path in csv_paths],
            *[path.read_text(encoding="utf-8") for path in md_paths],
        ]
    )
    return summary, rows, output_text


def collect_rows(
    summary: dict[str, Any], json_paths: list[Path], csv_paths: list[Path]
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []

    for key in ("rows", "grid_rows", "scaling_rows", "budget_rows"):
        value = summary.get(key)
        if isinstance(value, list):
            rows.extend(row for row in value if isinstance(row, dict))

    for path in json_paths:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, list):
            rows.extend(row for row in payload if isinstance(row, dict))
        elif isinstance(payload, dict):
            for key in ("rows", "grid_rows", "scaling_rows", "budget_rows"):
                value = payload.get(key)
                if isinstance(value, list):
                    rows.extend(row for row in value if isinstance(row, dict))

    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))

    return dedupe_grid_rows(rows)


def dedupe_grid_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deduped: dict[tuple[float, float], dict[str, Any]] = {}
    for row in rows:
        delta = number_at(row, "delta", "delta_over_b")
        reynolds = number_at(row, "reynolds", "re", "reynolds_core")
        if delta is None or reynolds is None:
            continue
        deduped.setdefault((delta, reynolds), row)
    return list(deduped.values())


def normalized_key(key: str) -> str:
    return "".join(ch for ch in key.lower() if ch.isalnum())


def value_at(row: dict[str, Any], *names: str) -> Any:
    normalized_names = {normalized_key(name) for name in names}
    for key, value in row.items():
        if normalized_key(str(key)) in normalized_names:
            return value
    return None


def number_at(row: dict[str, Any], *names: str) -> float | None:
    value = value_at(row, *names)
    if value is None or value == "":
        return None
    return float(value)


def bool_at(row: dict[str, Any], *names: str) -> bool:
    value = value_at(row, *names)
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        lowered = value.strip().lower().replace("_", "-")
        if lowered in {"true", "1", "yes", "pass", "passed", "ok"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "blocked", "fail-closed"}:
            return False
    raise AssertionError(f"expected boolean-like value for {names}, got {value!r}")


def summary_bool(summary: dict[str, Any], *names: str) -> bool:
    value = value_at(summary, *names)
    assert value is not None, f"summary missing one of {names}"
    return bool_at({"value": value}, "value")


def expected_viscous_window(delta_over_b: float, reynolds_core: float) -> bool:
    return reynolds_core * delta_over_b > (1.0 / delta_over_b) ** 2


def test_flux_budget_scaling_writes_fail_closed_artifacts(tmp_path: Path) -> None:
    summary, _rows, output_text = run_scaling(tmp_path)

    assert summary_bool(summary, "complete") is False
    assert summary_bool(summary, "clay", "clay_promoted", "clay_navier_stokes_promoted") is False
    assert "kstar" in output_text.lower()
    assert "proved" in output_text.lower() or "not_proved" in output_text.lower()
    assert "true" not in {
        str(value_at(summary, "kstar_threshold_proved", "finite_kstar_collapse_closed")).lower()
    }


def test_rows_cover_requested_delta_reynolds_grid(tmp_path: Path) -> None:
    _summary, rows, _output_text = run_scaling(tmp_path)

    observed = {
        (number_at(row, "delta", "delta_over_b"), number_at(row, "reynolds", "re", "reynolds_core"))
        for row in rows
    }
    expected = {(delta, reynolds) for delta in DELTAS for reynolds in REYNOLDS}
    assert observed == expected


def test_elliptic_factor_decreases_with_thinner_cores(tmp_path: Path) -> None:
    _summary, rows, _output_text = run_scaling(tmp_path)

    for reynolds in REYNOLDS:
        by_delta = sorted(
            (
                number_at(row, "delta"),
                number_at(row, "elliptic_factor", "ellipticfactor"),
            )
            for row in rows
            if math.isclose(number_at(row, "reynolds", "re", "reynolds_core") or -1.0, reynolds)
        )
        assert len(by_delta) == len(DELTAS)
        factors_from_thinnest_to_thickest = [factor for _delta, factor in by_delta]
        assert all(factor is not None for factor in factors_from_thinnest_to_thickest)
        assert factors_from_thinnest_to_thickest == sorted(
            factors_from_thinnest_to_thickest
        )


def test_viscous_window_and_certified_margin_follow_formula(tmp_path: Path) -> None:
    _summary, rows, _output_text = run_scaling(tmp_path)

    for row in rows:
        delta = number_at(row, "delta", "delta_over_b")
        reynolds = number_at(row, "reynolds", "re", "reynolds_core")
        assert delta is not None
        assert reynolds is not None

        viscous_ok = bool_at(row, "viscous_ok", "viscous_window_ok", "viscous_window")
        assert viscous_ok is expected_viscous_window(delta, reynolds)

        margin = number_at(row, "certified_surplus_margin", "certifiedsurplusmargin")
        assert margin is not None
        if viscous_ok:
            assert margin > 0
        else:
            assert margin <= 0

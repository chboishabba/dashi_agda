from __future__ import annotations

import csv
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_sprint130_viscous_dominance_sampler.py"


def run_sampler(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], Path]:
    out_dir = tmp_path / SCRIPT.stem
    env = os.environ.copy()
    env["TMPDIR"] = str(tmp_path)
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
        env=env,
    )
    return result, out_dir


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(out_dir.glob("*.csv")),
        sorted(out_dir.glob("*.md")),
    )


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_csv(paths: list[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend({"_csv_name": path.name, **row} for row in csv.DictReader(handle))
    return rows


def numberish(value: Any) -> Fraction | None:
    if isinstance(value, bool) or value is None or value == "":
        return None
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        return Fraction(str(value))
    if isinstance(value, str):
        text = value.strip()
        try:
            return Fraction(text)
        except ValueError:
            try:
                return Fraction(str(float(text)))
            except ValueError:
                return None
    return None


def normalized(row: dict[str, Any]) -> dict[str, Any]:
    return {"".join(ch for ch in key.lower() if ch.isalnum()): value for key, value in row.items()}


def row_number(row: dict[str, Any], *names: str) -> Fraction | None:
    data = normalized(row)
    for name in names:
        value = data.get("".join(ch for ch in name.lower() if ch.isalnum()))
        parsed = numberish(value)
        if parsed is not None:
            return parsed
    return None


def row_ratio(row: dict[str, Any]) -> Fraction | None:
    data = normalized(row)
    for key, value in data.items():
        if "ratio" in key:
            parsed = numberish(value)
            if parsed is not None:
                return parsed
    return None


def summary_json(json_paths: list[Path]) -> dict[str, Any]:
    candidates = [path for path in json_paths if "summary" in path.name.lower()]
    assert candidates, f"missing summary JSON in {[path.name for path in json_paths]}"
    summary = load_json(candidates[0])
    assert isinstance(summary, dict), f"summary is not a JSON object: {candidates[0].name}"
    return summary


def report_text(md_paths: list[Path]) -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in md_paths)


def test_sprint130_viscous_dominance_sampler_script_exists() -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"


def test_sprint130_viscous_dominance_sampler_cli_writes_complete_outputs(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_sampler(tmp_path)

    json_paths, csv_paths, md_paths = artifact_paths(out_dir)
    assert result.returncode == 0, result.stdout + result.stderr
    assert json_paths, "sampler did not write JSON output"
    assert csv_paths, "sampler did not write CSV rows output"
    assert md_paths, "sampler did not write Markdown report"
    assert any("row" in path.name.lower() for path in csv_paths), [path.name for path in csv_paths]

    summary = summary_json(json_paths)
    assert summary["viscous_dominance_obstruction"] is True
    assert summary["hou_luo_ns_route_obstructed"] is True
    assert summary["complete"] is True
    assert summary["clay_navier_stokes_promoted"] is False


def test_sprint130_rows_show_viscous_ratio_grows_as_tau_decreases(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_sampler(tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr

    _json_paths, csv_paths, _md_paths = artifact_paths(out_dir)
    rows = load_csv(csv_paths)
    assert rows, "sampler did not record CSV rows"
    assert any((row_number(row, "beta", "beta_fraction") or 0) > 0 for row in rows)

    grouped: dict[tuple[Fraction, Fraction], list[tuple[Fraction, Fraction]]] = defaultdict(list)
    for row in rows:
        beta = row_number(row, "beta", "beta_fraction")
        nu = row_number(row, "nu", "viscosity")
        tau = row_number(row, "tau", "time_to_blowup")
        ratio = row_ratio(row)
        if beta is None or nu is None or tau is None or ratio is None or beta <= 0:
            continue
        grouped[(beta, nu)].append((tau, ratio))

    monotone_groups = 0
    for samples in grouped.values():
        unique = sorted(set(samples), reverse=True)
        if len(unique) < 2:
            continue
        ratios = [ratio for _tau, ratio in unique]
        if all(left < right for left, right in zip(ratios, ratios[1:])):
            monotone_groups += 1

    assert monotone_groups, "no fixed beta/nu row family had increasing ratio as tau decreased"


def test_sprint130_report_records_scaling_and_alpha_window(tmp_path: Path) -> None:
    assert SCRIPT.exists(), f"missing sampler script: {SCRIPT.relative_to(REPO_ROOT)}"
    result, out_dir = run_sampler(tmp_path)
    assert result.returncode == 0, result.stdout + result.stderr

    _json_paths, _csv_paths, md_paths = artifact_paths(out_dir)
    text = report_text(md_paths)
    compact = re.sub(r"[\s`$\\{}()]", "", text.lower())

    assert (
        "nu*tau^-3beta" in compact
        or "nu*tau**-3*beta" in compact
        or "nu*tau^(-3beta)" in text.lower().replace(" ", "")
        or "nu*tau^(-3*beta)" in text.lower().replace(" ", "")
    ), "report should mention the nu * tau^(-3 beta) viscous scaling"
    assert re.search(r"1\s*<\s*alpha\s*<\s*3\s*/\s*2", text.lower()), (
        "report should mention the alpha window 1 < alpha < 3/2"
    )

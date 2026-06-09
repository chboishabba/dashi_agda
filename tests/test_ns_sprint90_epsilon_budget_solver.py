from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


SCRIPT = Path("scripts/ns_sprint90_epsilon_budget_solver.py")
OUT_NAME = "ns_sprint90_epsilon_budget_solver"
REQUIRED_RESIDUAL_GATE = "PointwiseH1TailWithIndependentEpsilonCoefficient"


def run_solver(tmp_path: Path) -> tuple[Path, dict[str, Any], list[dict[str, str]], str]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 90 epsilon budget solver script is not present.")

    out_dir = tmp_path / OUT_NAME
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, "solver did not write JSON output"
    assert csv_paths, "solver did not write CSV output"
    assert md_paths, "solver did not write Markdown output"

    summary_path = next(
        (
            path
            for path in json_paths
            if path.name.endswith("_summary.json") or "summary" in path.name
        ),
        json_paths[0],
    )
    summary = json.loads(summary_path.read_text())

    rows: list[dict[str, str]] = []
    for path in csv_paths:
        with path.open(newline="") as handle:
            rows.extend(csv.DictReader(handle))

    artifact_text = "\n".join(
        [json.dumps(summary, sort_keys=True)]
        + [path.read_text() for path in csv_paths]
        + [path.read_text() for path in md_paths]
    )
    return out_dir, summary, rows, artifact_text


def as_bool(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"true", "1", "yes", "closed", "pass"}
    return False


def normalized(value: object) -> str:
    return str(value).replace("_", "-").strip().lower()


def first_present(summary: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        if key in summary:
            return summary[key]
    raise AssertionError(f"missing expected summary key alias: {', '.join(keys)}")


def row_text(row: dict[str, str]) -> str:
    return " ".join(str(value) for value in row.values())


def test_ns_sprint90_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir, summary, _rows, _artifact_text = run_solver(tmp_path)

    assert first_present(
        summary,
        ("contract", "solver_contract", "audit_contract"),
    ) == "ns_sprint90_epsilon_budget_solver"
    assert list(out_dir.glob("*.json"))
    assert list(out_dir.glob("*.csv"))
    assert list(out_dir.glob("*.md"))


def test_ns_sprint90_candidate_k_laws_include_expected_nu_powers(
    tmp_path: Path,
) -> None:
    _out_dir, _summary, _rows, artifact_text = run_solver(tmp_path)

    compact = artifact_text.replace(" ", "").lower()
    expected_laws = (
        ("nu^-1", "nu**-1", "nu^{-1}", "ν^-1", "ν^{-1}"),
        ("nu^-4/3", "nu**(-4/3)", "nu^{-4/3}", "ν^-4/3", "ν^{-4/3}"),
        ("nu^-2", "nu**-2", "nu^{-2}", "ν^-2", "ν^{-2}"),
    )
    for aliases in expected_laws:
        assert any(alias in compact for alias in aliases), aliases


def test_ns_sprint90_no_allowed_route_closes_both_required_conditions(
    tmp_path: Path,
) -> None:
    _out_dir, _summary, rows, artifact_text = run_solver(tmp_path)

    route_rows = [
        row
        for row in rows
        if "route" in " ".join(row.keys()).lower()
        or "candidate" in " ".join(row.keys()).lower()
    ]
    assert route_rows, "expected CSV rows describing candidate budget routes"

    allowed_and_closes_both = []
    for row in route_rows:
        text = row_text(row).lower()
        is_allowed = any(
            as_bool(value)
            for key, value in row.items()
            if "allowed" in key.lower()
            or "admissible" in key.lower()
            or "valid" in key.lower()
        )
        closes_pointwise_h1 = any(
            as_bool(value)
            for key, value in row.items()
            if "pointwise" in key.lower() and "h1" in key.lower() and "tail" in key.lower()
        )
        closes_independent_epsilon = any(
            as_bool(value)
            for key, value in row.items()
            if "independent" in key.lower() and "epsilon" in key.lower()
        )
        if is_allowed and closes_pointwise_h1 and closes_independent_epsilon:
            allowed_and_closes_both.append(row)

        assert not (
            "allowed" in text
            and "pointwise h1 tail" in text
            and "independent epsilon" in text
            and "closes both" in text
        )

    assert allowed_and_closes_both == []
    assert "closes both pointwise h1 tail and independent epsilon" not in (
        artifact_text.lower()
    )


def test_ns_sprint90_route_decision_and_required_residual_gate(tmp_path: Path) -> None:
    _out_dir, summary, _rows, artifact_text = run_solver(tmp_path)

    route_decision = normalized(
        first_present(summary, ("route_decision", "decision", "solver_decision"))
    )
    assert route_decision in {"fail-closed", "fail-open"}

    residual_gate = first_present(
        summary,
        (
            "required_residual_gate",
            "residual_gate",
            "next_required_gate",
            "required_gate",
        ),
    )
    assert residual_gate == REQUIRED_RESIDUAL_GATE
    assert REQUIRED_RESIDUAL_GATE in artifact_text

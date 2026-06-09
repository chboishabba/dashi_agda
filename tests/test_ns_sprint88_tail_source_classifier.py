from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


SCRIPT = Path("scripts/ns_sprint88_tail_source_classifier.py")


def run_classifier(tmp_path: Path) -> tuple[Path, dict[str, Any]]:
    if not SCRIPT.exists():
        pytest.skip("Sprint 88 tail source classifier script is not present.")

    out_dir = tmp_path / "ns_sprint88_tail_source_classifier"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )

    summary_path = out_dir / "ns_sprint88_tail_source_classifier_summary.json"
    assert summary_path.exists()
    return out_dir, json.loads(summary_path.read_text())


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def as_bool(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"true", "1", "yes"}
    return False


def first_present(summary: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        if key in summary:
            return summary[key]
    raise AssertionError(f"missing expected summary key alias: {', '.join(keys)}")


def normalized_text(row: dict[str, str]) -> str:
    return " ".join(str(value).lower() for value in row.values())


def source_rows(out_dir: Path, summary: dict[str, Any]) -> list[dict[str, str]]:
    table = out_dir / summary["source_table"]
    assert table.exists(), "expected a source classification CSV table"
    return read_csv(table)


def conditionally_sufficient(row: dict[str, str]) -> bool:
    return as_bool(row.get("sufficient_for_pointwise_absorption"))


def pointwise_h1_tail(row: dict[str, str]) -> bool:
    return any(
        as_bool(value)
        for key, value in row.items()
        if "pointwise" in key.lower() and "h1" in key.lower() and "tail" in key.lower()
    )


def independent_epsilon_coefficient(row: dict[str, str]) -> bool:
    return any(
        as_bool(value)
        for key, value in row.items()
        if "independent" in key.lower()
        and "epsilon" in key.lower()
        and "coefficient" in key.lower()
    )


def test_ns_sprint88_tail_classifier_records_five_sources(tmp_path: Path) -> None:
    out_dir, summary = run_classifier(tmp_path)
    rows = source_rows(out_dir, summary)

    assert first_present(
        summary,
        ("contract", "classifier_contract"),
    ) == "ns_sprint88_tail_source_classifier"
    assert first_present(summary, ("source_count", "tail_source_count")) == 5
    assert len(rows) == 5

    row_text = "\n".join(normalized_text(row) for row in rows)
    for required in ("kstar", "leray", "time-integrated"):
        assert required in row_text


def test_ns_sprint88_only_pointwise_h1_tail_with_independent_epsilon_is_sufficient(
    tmp_path: Path,
) -> None:
    out_dir, summary = run_classifier(tmp_path)
    rows = source_rows(out_dir, summary)

    insufficient = [
        row
        for row in rows
        if row["source_name"]
        in {"KStarL2Tail", "LerayEnergyPointwise", "TimeIntegratedDissipation"}
    ]
    assert len(insufficient) == 3
    assert not any(conditionally_sufficient(row) for row in insufficient)

    sufficient = [row for row in rows if conditionally_sufficient(row)]
    assert sufficient == []

    assert first_present(
        summary,
        (
            "only_pointwise_h1_tail_with_independent_epsilon_conditionally_sufficient",
            "only_combined_pointwise_h1_independent_epsilon_conditionally_sufficient",
            "pointwise_absorption_rule",
        ),
    ) == (
        "sufficient iff one source supplies pointwise H1 tail and an "
        "independent epsilon coefficient"
    )
    assert summary["next_required_gate"] == (
        "PointwiseH1TailWithIndependentEpsilonCoefficient"
    )


def test_ns_sprint88_fails_closed_without_unconditional_or_clay_promotion(
    tmp_path: Path,
) -> None:
    _out_dir, summary = run_classifier(tmp_path)

    assert first_present(
        summary,
        ("unconditional_closure", "unconditional_absorption_closed"),
    ) is False
    assert first_present(
        summary,
        ("clay_navier_stokes_promoted", "clay_ns_promoted"),
    ) is False
    assert first_present(
        summary,
        ("clay_promotion_recorded_false", "clay_ns_promotion_recorded_false"),
    ) is True

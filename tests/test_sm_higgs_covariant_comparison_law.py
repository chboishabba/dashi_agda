from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "sm_higgs_covariant_comparison_law.py"
RECEIPT = (
    ROOT
    / "outputs"
    / "sm_higgs_hepdata_receipts"
    / "sm_higgs_observed_shape_receipt.json"
)
BASELINE = ROOT / "tests" / "fixtures" / "sm_higgs_baseline_fixture.json"


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def gate(summary: dict[str, Any], name: str) -> Any:
    gates = summary.get("gates", {})
    if name in gates:
        return gates[name]
    return summary.get(name)


def test_cli_emits_covariant_comparison_json_and_markdown(tmp_path: Path) -> None:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--receipt",
            str(RECEIPT),
            "--baseline",
            str(BASELINE),
            "--generated-at",
            "2026-06-07T00:00:00+00:00",
            "--output-dir",
            str(tmp_path),
        ],
        check=True,
        cwd=ROOT,
    )

    summary_path = tmp_path / "sm_higgs_covariant_comparison_summary.json"
    rows_path = tmp_path / "sm_higgs_covariant_comparison_rows.json"
    markdown_path = tmp_path / "sm_higgs_covariant_comparison_law.md"

    assert summary_path.exists()
    assert rows_path.exists()
    assert markdown_path.exists()

    summary = load_json(summary_path)
    rows_payload = load_json(rows_path)
    markdown = markdown_path.read_text(encoding="utf-8").lower()

    assert summary["schema"] == "dashi-sm-higgs-covariant-comparison-law-v1"
    assert summary["schema_version"] == "1.0.0"
    assert rows_payload["schema"] == summary["schema"]
    assert rows_payload["schema_version"] == summary["schema_version"]
    assert "non-promoting" in markdown or "non promoting" in markdown


def test_cli_rows_have_fixture_covariance_and_chi2_payloads(tmp_path: Path) -> None:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--receipt",
            str(RECEIPT),
            "--baseline",
            str(BASELINE),
            "--generated-at",
            "2026-06-07T00:00:00+00:00",
            "--output-dir",
            str(tmp_path),
        ],
        check=True,
        cwd=ROOT,
    )

    summary = load_json(tmp_path / "sm_higgs_covariant_comparison_summary.json")
    rows_payload = load_json(tmp_path / "sm_higgs_covariant_comparison_rows.json")
    rows = rows_payload.get("comparison_rows", rows_payload.get("rows", []))

    assert len(rows) >= 4
    assert summary.get("comparison_row_count", len(rows)) >= 4

    for row in rows:
        assert "observable" in row
        assert row["covariance_positive_definite"] is True
        assert row["dof"] > 0
        assert row["chi2"] >= 0
        assert row["reduced_chi2"] >= 0


def test_fixture_comparison_is_not_promoted_without_authority_acceptance(
    tmp_path: Path,
) -> None:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--receipt",
            str(RECEIPT),
            "--baseline",
            str(BASELINE),
            "--generated-at",
            "2026-06-07T00:00:00+00:00",
            "--output-dir",
            str(tmp_path),
        ],
        check=True,
        cwd=ROOT,
    )

    summary = load_json(tmp_path / "sm_higgs_covariant_comparison_summary.json")

    if gate(summary, "accepted_authority_token_present") is not True:
        assert gate(summary, "empirical_validation_promoted") is False
        assert gate(summary, "sm_higgs_observable_promoted") is False
        assert gate(summary, "standard_model_promoted") is False

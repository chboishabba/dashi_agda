from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_stellar_composition_proxy_diagnostic.py"

OUTPUT_STEM = "stellar_composition_proxy_diagnostic"
FAIL_CLOSED_FLAGS = {
    "carrier_internal_prediction": False,
    "stellar_evolution_promoted": False,
    "solar_instability_claim_promoted": False,
    "external_baseline_or_proxy_only": True,
}


def run_diagnostic(tmp_path: Path, *extra_args: str) -> tuple[dict[str, Any], Path]:
    out_dir = tmp_path / "stellar_proxy"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            *extra_args,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )

    stdout_payload = json.loads(proc.stdout)
    file_payload = json.loads(
        (out_dir / f"{OUTPUT_STEM}.json").read_text(encoding="utf-8")
    )
    assert stdout_payload == file_payload
    return file_payload, out_dir


def rows_by_label(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = payload["rows"]
    return {row["label"]: row for row in rows}


def test_default_run_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    payload, out_dir = run_diagnostic(tmp_path)

    json_path = out_dir / f"{OUTPUT_STEM}.json"
    csv_path = out_dir / f"{OUTPUT_STEM}.csv"
    md_path = out_dir / f"{OUTPUT_STEM}.md"

    assert json_path.exists()
    assert csv_path.exists()
    assert md_path.exists()
    assert payload["diagnostic"] == OUTPUT_STEM
    assert payload["status"] == "proxy_only_no_promotion"
    assert payload["output_paths"] == {
        "json": str(json_path),
        "csv": str(csv_path),
        "markdown": str(md_path),
    }

    with csv_path.open(newline="", encoding="utf-8") as handle:
        csv_rows = list(csv.DictReader(handle))
    assert len(csv_rows) == len(payload["rows"])
    assert {row["label"] for row in csv_rows} == {row["label"] for row in payload["rows"]}

    markdown = md_path.read_text(encoding="utf-8")
    assert OUTPUT_STEM in markdown
    assert "proxy_only_no_promotion" in markdown


def test_default_receipt_is_fail_closed(tmp_path: Path) -> None:
    payload, _out_dir = run_diagnostic(tmp_path)

    assert payload["fail_closed_flags"] == FAIL_CLOSED_FLAGS
    assert payload["promotion"]["state"] == "blocked"
    assert payload["promotion"]["flags"] == FAIL_CLOSED_FLAGS
    assert "missing_carrier_derived_matter_force_law" in payload["promotion"]["blockers"]
    assert "missing_empirical_validation_receipt" in payload["promotion"]["blockers"]

    for row in payload["rows"]:
        assert row["claim_boundary"] == FAIL_CLOSED_FLAGS
        assert row["solar_instability_claim"] is False


def test_default_cases_include_reference_and_hydrogen_perturbations(
    tmp_path: Path,
) -> None:
    payload, _out_dir = run_diagnostic(tmp_path)
    rows = rows_by_label(payload)

    assert set(rows) == {
        "solar_reference",
        "hydrogen_minus_0.03",
        "hydrogen_plus_0.03",
    }
    assert rows["solar_reference"]["baseline_normalized"] is True
    assert rows["solar_reference"]["support_proxy_ratio"] == 1.0
    assert rows["solar_reference"]["energy_generation_proxy_ratio"] == 1.0
    assert rows["hydrogen_minus_0.03"]["baseline_normalized"] is False
    assert rows["hydrogen_plus_0.03"]["baseline_normalized"] is False


def test_invalid_composition_is_rejected(tmp_path: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(tmp_path / "invalid"),
            "--composition",
            "bad_negative",
            "-0.1",
            "1.0",
            "0.1",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )

    assert proc.returncode != 0
    assert "composition" in proc.stderr.lower()
    assert "bad_negative" in proc.stderr


def test_non_normalized_composition_requires_normalize_flag(tmp_path: Path) -> None:
    args = [
        "--out-dir",
        str(tmp_path / "non_normalized_rejected"),
        "--composition",
        "raw_case",
        "0.70",
        "0.28",
        "0.03",
    ]
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )

    assert proc.returncode != 0
    assert "normalize" in proc.stderr.lower()


def test_normalize_flag_accepts_and_records_raw_composition(tmp_path: Path) -> None:
    payload, _out_dir = run_diagnostic(
        tmp_path,
        "--composition",
        "raw_case",
        "0.70",
        "0.28",
        "0.03",
        "--normalize",
    )
    row = rows_by_label(payload)["raw_case"]

    assert row["input_composition"] == {"X": 0.70, "Y": 0.28, "Z": 0.03}
    assert row["composition_normalized"] is True
    assert row["composition"] == {
        "X": 0.70 / 1.01,
        "Y": 0.28 / 1.01,
        "Z": 0.03 / 1.01,
    }
    assert row["claim_boundary"] == FAIL_CLOSED_FLAGS


def test_perturbation_rows_do_not_claim_solar_instability(tmp_path: Path) -> None:
    payload, _out_dir = run_diagnostic(tmp_path)
    rows = rows_by_label(payload)

    for label in ("hydrogen_minus_0.03", "hydrogen_plus_0.03"):
        row = rows[label]
        assert row["solar_instability_claim"] is False
        assert row["stability_observable"]["claim"] == "no_solar_instability_claim"
        assert row["stability_observable"]["promoted"] is False
        assert row["claim_boundary"]["solar_instability_claim_promoted"] is False

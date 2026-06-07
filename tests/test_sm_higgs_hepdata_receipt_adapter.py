from __future__ import annotations

import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.sm_higgs_hepdata_receipt_adapter import (  # type: ignore[import-not-found]
    DEFAULT_DASHIQ_ROOT,
    SCHEMA,
    build_receipts,
    write_receipts,
)


def test_build_receipts_binds_dashiq_higgs_hepdata_sources() -> None:
    receipts = build_receipts(
        DEFAULT_DASHIQ_ROOT,
        generated_at="2026-06-07T00:00:00+00:00",
        run_observed=False,
    )

    observed = receipts["observed"]
    pseudo = receipts["pseudo"]
    summary = receipts["summary"]

    assert observed["schema"] == SCHEMA
    assert observed["hepdata_record"] == "137886"
    assert observed["observable_count"] == 4
    assert observed["full_covariance_surface_present"] is True
    assert observed["sm_relative_baseline_present"] is False
    assert observed["empirical_validation_promoted"] is False
    assert observed["live_observed_results"] == []

    assert pseudo["observable_count"] == 3
    assert set(pseudo["injection_modes"]) >= {"tilt", "curvature", "two_regime", "anisotropy"}
    assert set(pseudo["projection_modes"]) >= {"raw", "cumulative", "valuation", "angular"}
    assert pseudo["observed_new_physics_claim"] is False

    assert summary["source_file_count"] == 4
    assert summary["gates"]["source_checksums_bound"] is True
    assert summary["gates"]["sm_relative_baseline_present"] is False
    assert summary["gates"]["accepted_authority_token_present"] is False
    assert summary["gates"]["standard_model_promoted"] is False
    assert all(len(source["sha256"]) == 64 for source in observed["source_files"])


def test_write_receipts_emits_three_json_files_and_markdown(tmp_path: Path) -> None:
    receipts = build_receipts(
        DEFAULT_DASHIQ_ROOT,
        generated_at="2026-06-07T00:00:00+00:00",
        run_observed=False,
    )

    write_receipts(receipts, tmp_path)

    expected = {
        "sm_higgs_observed_shape_receipt.json",
        "sm_higgs_pseudo_detectability_receipt.json",
        "sm_higgs_adapter_summary.json",
        "sm_higgs_hepdata_receipt_adapter.md",
    }
    assert expected <= {path.name for path in tmp_path.iterdir()}

    summary = json.loads((tmp_path / "sm_higgs_adapter_summary.json").read_text())
    assert summary["schema"] == SCHEMA
    assert summary["observed_shape_receipt"] == "sm_higgs_observed_shape_receipt.json"
    assert summary["pseudo_detectability_receipt"] == "sm_higgs_pseudo_detectability_receipt.json"

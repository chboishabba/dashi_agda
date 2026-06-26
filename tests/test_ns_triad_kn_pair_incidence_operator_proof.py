from __future__ import annotations

from functools import lru_cache
import json
import math
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_pair_incidence_operator_proof.py"
CANONICAL_OUTPUT_DIR = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_pair_incidence_operator_proof_20260624"
)
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNPairIncidenceOperatorReceipt.agda"
)


@lru_cache(maxsize=1)
def run_script() -> tuple[dict[str, Any], str]:
    assert SCRIPT.is_file(), f"missing {SCRIPT}"
    canonical_json = CANONICAL_OUTPUT_DIR / "summary.json"
    canonical_md = CANONICAL_OUTPUT_DIR / "summary.md"
    if canonical_json.is_file() and canonical_md.is_file():
        payload = json.loads(canonical_json.read_text(encoding="utf-8"))
        return payload, canonical_md.read_text(encoding="utf-8")
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_pair_incidence_operator_proof"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--output-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    text = result.stdout + "\n" + result.stderr
    assert result.returncode == 0, text
    summary_json = out_dir / "summary.json"
    summary_md = out_dir / "summary.md"
    assert summary_json.is_file(), text
    assert summary_md.is_file(), text
    payload = json.loads(summary_json.read_text(encoding="utf-8"))
    return payload, text + "\n" + summary_md.read_text(encoding="utf-8")


def test_pair_incidence_operator_proof_is_fail_closed() -> None:
    payload, text = run_script()

    assert payload["status"] == "ok"
    assert payload["candidate_only"] is True
    assert payload["fail_closed"] is True
    assert payload["canonical_operator_name"] == "exact_scripted_pair_incidence_operator"
    assert payload["sampled_schur_script_match"] is True
    assert payload["sampled_schur_adversarial_match"] is True
    assert payload["reconciliation_verdict"] == "different_object"
    assert payload["forced_tail_row_count"] == 4
    assert payload["adversarial_row_count"] == 4
    assert isinstance(payload["started_at"], str) and payload["started_at"]
    assert isinstance(payload["finished_at"], str) and payload["finished_at"]
    assert float(payload["elapsed_ms"]) >= 0.0
    assert payload["log_entries"], payload
    assert payload["log_entries"][0]["message"] == "started pair-incidence operator proof run"
    assert payload["log_entries"][-1]["message"] == "wrote pair-incidence proof artifacts"
    assert "exact_scripted_pair_incidence_operator" in text
    assert "different_object" in text

    for row in payload["forced_tail_rows"]:
        assert row["row_sum_sup"] > 0.0
        assert row["column_sum_sup"] > 0.0
        assert row["schur_bound"] > 0.0
        assert row["cross_edge_count"] > 0
    for row in payload["adversarial_rows"]:
        assert row["row_sum_sup"] > 0.0
        assert row["column_sum_sup"] > 0.0
        assert row["schur_bound"] > 0.0


def test_pair_incidence_operator_proof_carries_sampled_scaling() -> None:
    payload, _text = run_script()
    forced_fit = payload["fits"]["forced_tail_schur_bound_vs_N"]
    forced_col_fit = payload["fits"]["forced_tail_column_sum_sup_vs_N"]
    match = payload["sampled_schur_match_details"]

    assert forced_fit["count"] == 4
    assert forced_col_fit["count"] == 4
    assert -1.05 < forced_fit["log_log_slope"] < -0.8, forced_fit
    assert forced_col_fit["log_log_slope"] < -1.0, forced_col_fit
    assert match["all_rows_match_to_1e12"] is True
    assert match["max_relative_difference"] is not None
    assert math.isclose(float(match["max_relative_difference"]), 0.0, abs_tol=1e-15)


def test_pair_incidence_operator_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNPairIncidenceOperatorReceipt" in text
    assert "ns_triad_kn_pair_incidence_operator_proof_20260624/summary.json" in text
    assert 'canonicalOperatorName' in text
    assert '"exact_scripted_pair_incidence_operator"' in text
    assert 'theoremPromoted ≡ false' in text

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
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_lft_definition_reconciliation.py"
CANONICAL_OUTPUT_DIR = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_lft_definition_reconciliation_20260624"
)
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNLFTDefinitionReconciliationReceipt.agda"
)


@lru_cache(maxsize=1)
def run_script() -> tuple[dict[str, Any], str]:
    assert SCRIPT.is_file(), f"missing {SCRIPT}"
    canonical_json = CANONICAL_OUTPUT_DIR / "summary.json"
    canonical_md = CANONICAL_OUTPUT_DIR / "summary.md"
    if canonical_json.is_file() and canonical_md.is_file():
        payload = json.loads(canonical_json.read_text(encoding="utf-8"))
        return payload, canonical_md.read_text(encoding="utf-8")
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_lft_definition_reconciliation"
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


def test_definition_reconciliation_is_fail_closed() -> None:
    payload, text = run_script()

    assert payload["status"] == "ok"
    assert payload["candidate_only"] is True
    assert payload["fail_closed"] is True
    assert payload["overall_verdict"] == "different_object"
    assert payload["row_count"] == 8
    assert isinstance(payload["started_at"], str) and payload["started_at"]
    assert isinstance(payload["finished_at"], str) and payload["finished_at"]
    assert float(payload["elapsed_ms"]) >= 0.0
    assert payload["log_entries"], payload
    assert payload["log_entries"][0]["message"] == "started definition reconciliation audit"
    assert payload["log_entries"][-1]["message"] == "wrote definition reconciliation artifacts"
    assert "different_object" in text

    rows = payload["rows"]
    assert [int(row["N"]) for row in rows] == [6, 6, 8, 8, 10, 10, 12, 12]
    assert {row["profile_id"] for row in rows} == {"forced_tail", "adversarial_worst_tail_support"}
    for row in rows:
        assert row["verdict"] == "different_object"
        assert row["script_active_cross_pair_count"] > 0
        assert row["bare_positive_cross_pair_count"] > 0
        assert row["column_sum_script"] > 0.0
        assert row["column_sum_bare"] > 0.0
        assert row["schur_bound_script"] > 0.0
        assert row["schur_bound_bare"] > 0.0
        assert math.isfinite(float(row["support_jaccard"]))
        assert row["worst_script_pair"] is not None


def test_definition_reconciliation_captures_scaling_gap() -> None:
    payload, _text = run_script()
    fits = payload["fits"]

    script_col_fit = fits["forced_tail_column_sum_script_vs_N"]
    bare_col_fit = fits["forced_tail_column_sum_bare_vs_N"]
    script_schur_fit = fits["forced_tail_schur_bound_script_vs_N"]
    bare_schur_fit = fits["forced_tail_schur_bound_bare_vs_N"]

    assert script_col_fit["count"] == 4
    assert bare_col_fit["count"] == 4
    assert script_schur_fit["count"] == 4
    assert bare_schur_fit["count"] == 4
    assert script_col_fit["log_log_slope"] < -1.0
    assert bare_col_fit["log_log_slope"] > 1.0
    assert script_schur_fit["log_log_slope"] < -0.8
    assert bare_schur_fit["log_log_slope"] > 0.0


def test_definition_reconciliation_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNLFTDefinitionReconciliationReceipt" in text
    assert 'verdict ≡ "different_object"' in text
    assert 'theoremPromoted ≡ false' in text

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
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_lft_kernel_acl_match.py"
CANONICAL_OUTPUT_DIR = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_lft_kernel_acl_match_20260624"
)
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNMixedTailACLKernelMatchReceipt.agda"
)


@lru_cache(maxsize=1)
def run_script() -> tuple[dict[str, Any], str]:
    assert SCRIPT.is_file(), f"missing {SCRIPT}"
    canonical_json = CANONICAL_OUTPUT_DIR / "summary.json"
    canonical_md = CANONICAL_OUTPUT_DIR / "summary.md"
    if canonical_json.is_file() and canonical_md.is_file():
        payload = json.loads(canonical_json.read_text(encoding="utf-8"))
        return payload, canonical_md.read_text(encoding="utf-8")
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_lft_kernel_acl_match"
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


def test_kernel_match_audit_fails_closed() -> None:
    payload, text = run_script()

    assert payload["status"] == "ok"
    assert payload["candidate_only"] is True
    assert payload["fail_closed"] is True
    assert payload["kernel_match_status"] == "failed"
    assert payload["positive_sector_survives_acl"] is False
    assert payload["absolute_sector_survives_acl"] is False
    assert payload["schur_lift_available"] is False
    assert payload["profile_independent_bound_closed"] is False
    assert payload["profile_amplitude_factor_present"] is True
    assert payload["positive_sector_truncation_present"] is True
    assert payload["signed_acl_factor_survives"] is False
    assert payload["row_count"] == 4
    assert isinstance(payload["started_at"], str) and payload["started_at"]
    assert isinstance(payload["finished_at"], str) and payload["finished_at"]
    assert float(payload["elapsed_ms"]) >= 0.0
    assert payload["log_entries"], payload
    assert payload["log_entries"][0]["message"] == "started kernel match audit"
    assert payload["log_entries"][-1]["message"] == "wrote kernel match artifacts"
    assert "sqrt(pi_i*pi_j*pi_l)/3" in payload["exact_dashi_entry_formula"]
    assert "max(cos(phi_i+phi_j-phi_l),0)" in payload["exact_dashi_entry_formula"]
    assert "kernel match status" in text.lower()

    rows = payload["rows"]
    assert [int(row["N"]) for row in rows] == [6, 8, 10, 12]
    for row in rows:
        forced = row["forced_tail"]
        uniform = row["uniform_all_modes"]
        assert forced["positive_sector_only"] is True
        assert forced["signed_acl_factor_survives"] is False
        assert forced["absolute_acl_factor_survives"] is False
        assert forced["max_cross_entry_abs"] > 0.0
        assert uniform["max_cross_entry_abs"] > 0.0
        assert row["profile_dependence_ratio_max_cross_entry"] > 0.0


def test_kernel_match_audit_records_profile_dependence() -> None:
    payload, _text = run_script()
    stats = payload["profile_dependence_ratio_max_cross_entry_stats"]
    forced_stats = payload["forced_tail_n_pow_3_over_2_max_cross_entry_abs_stats"]

    assert stats["count"] == 4
    assert forced_stats["count"] == 4
    assert math.isfinite(float(stats["min"]))
    assert math.isfinite(float(stats["max"]))
    assert math.isfinite(float(forced_stats["min"]))
    assert math.isfinite(float(forced_stats["max"]))


def test_kernel_match_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNMixedTailACLKernelMatchReceipt" in text
    assert "kernelMatchStatus : String" in text
    assert 'kernelMatchStatus ≡ "failed"' in text
    assert 'theoremPromoted ≡ false' in text

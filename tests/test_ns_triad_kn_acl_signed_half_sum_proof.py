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
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_acl_signed_half_sum_proof.py"
CANONICAL_OUTPUT_DIR = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_acl_signed_half_sum_proof_20260624"
)
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNACLForkResolutionReceipt.agda"
)


@lru_cache(maxsize=1)
def run_script() -> tuple[dict[str, Any], str]:
    assert SCRIPT.is_file(), f"missing {SCRIPT}"
    canonical_json = CANONICAL_OUTPUT_DIR / "summary.json"
    canonical_md = CANONICAL_OUTPUT_DIR / "summary.md"
    if canonical_json.is_file() and canonical_md.is_file():
        payload = json.loads(canonical_json.read_text(encoding="utf-8"))
        return payload, canonical_md.read_text(encoding="utf-8")
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_acl_signed_half_sum_proof"
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


def test_acl_signed_half_sum_proof_resolves_fork() -> None:
    payload, text = run_script()

    assert payload["status"] == "ok"
    assert payload["candidate_only"] is True
    assert payload["fail_closed"] is True
    assert payload["fork_a_dead"] is True
    assert payload["fork_b_direct_positive_sector_only"] is True
    assert payload["row_count"] == 4
    assert isinstance(payload["started_at"], str) and payload["started_at"]
    assert isinstance(payload["finished_at"], str) and payload["finished_at"]
    assert float(payload["elapsed_ms"]) >= 0.0
    assert payload["log_entries"], payload
    assert payload["log_entries"][0]["message"] == "started analytic proof run"
    assert payload["log_entries"][-1]["message"] == "wrote proof artifacts"
    assert "Fork A is dead" in payload["analysis_read"]
    assert "positive_mass_ratio" in text

    expected_ks = [
        [0, 10, 0],
        [7, 7, 0],
        [5, 8, 3],
        [3, 9, 2],
    ]
    rows = payload["rows"]
    assert [row["representative_k"] for row in rows] == expected_ks
    for row in rows:
        closure = row["closure_angle_test"]
        acl = row["acl_first_harmonic_half_sum"]
        assert row["transverse_mode_count"] > 0
        assert closure["positive_count"] == 0
        assert closure["negative_count"] == row["transverse_mode_count"]
        assert math.isclose(float(closure["signed_to_absolute_ratio"]), 1.0, rel_tol=1e-12)
        assert abs(float(acl["signed_sum"])) <= 1.0e-12
        assert math.isclose(
            float(acl["positive_sum"]),
            float(acl["negative_sum"]),
            rel_tol=1e-12,
            abs_tol=1e-12,
        )
        assert float(acl["imbalance_ratio"]) <= 1.0e-12
        assert math.isclose(float(acl["positive_mass_ratio"]), 0.5, rel_tol=1e-12, abs_tol=1e-12)


def test_acl_signed_half_sum_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNACLForkResolutionReceipt" in text
    assert 'forkADead ≡ true' in text
    assert 'positiveBlockControlledByACL ≡ false' in text
    assert 'theoremPromoted ≡ false' in text

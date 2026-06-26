from __future__ import annotations

from functools import lru_cache
import json
import math
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_acl_schur_test_proof.py"
CANONICAL_OUTPUT_DIR = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_acl_schur_test_proof_20260624"
)
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNMixedTailACLOperatorNormAuditReceipt.agda"
)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = {normalize(key) for key in keys}
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted and isinstance(value, bool):
                values.append(value)
    return values


@lru_cache(maxsize=1)
def run_script() -> tuple[dict[str, Any], str]:
    assert SCRIPT.is_file(), f"missing {SCRIPT}"
    canonical_json = CANONICAL_OUTPUT_DIR / "summary.json"
    canonical_md = CANONICAL_OUTPUT_DIR / "summary.md"
    if canonical_json.is_file() and canonical_md.is_file():
        payload = json.loads(canonical_json.read_text(encoding="utf-8"))
        return payload, canonical_md.read_text(encoding="utf-8")
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_acl_schur_test"
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


def test_acl_schur_test_proof_emits_fail_closed_rows() -> None:
    payload, text = run_script()
    combined = normalize(json.dumps(payload, sort_keys=True)) + "\n" + normalize(text)

    assert payload["status"] == "ok"
    assert payload["candidate_only"] is True
    assert payload["fail_closed"] is True
    assert payload["row_count"] == 4
    assert payload["adversarial_row_count"] == 4
    assert isinstance(payload["started_at"], str) and payload["started_at"]
    assert isinstance(payload["finished_at"], str) and payload["finished_at"]
    assert float(payload["elapsed_ms"]) >= 0.0
    assert payload["log_entries"], payload
    assert payload["log_entries"][0]["message"] == "started analytic proof run"
    assert payload["log_entries"][-1]["message"] == "wrote proof artifacts"
    assert "schur_test_statement" in combined
    assert "finite_shell_only" in combined
    assert "n_times_schur_bound" in combined

    for key in (
        "theorem_promoted",
        "full_ns_promoted",
        "bkm_exclusion_proved",
        "clay_promoted",
    ):
        values = bool_values_for_keys(payload, key)
        assert values and all(value is False for value in values), (key, values)

    rows = payload["rows"]
    adversarial_rows = payload["adversarial_rows"]
    ns = [int(row["N"]) for row in rows]
    assert ns == [6, 8, 10, 12]
    for row in rows:
        assert row["cross_entry_sign"] == "nonpositive"
        assert row["row_sum_sup"] > 0.0
        assert row["column_sum_sup"] > 0.0
        assert row["schur_bound"] > 0.0
        assert row["N_times_schur_bound"] > 0.0
        expected = math.sqrt(float(row["row_sum_sup"]) * float(row["column_sum_sup"]))
        assert math.isclose(float(row["schur_bound"]), expected, rel_tol=1e-12)
        assert "worst_tail_mode" in row
        assert int(row["worst_tail_active_finite_k_count"]) > 0
    for row in adversarial_rows:
        assert row["candidate_only"] is True
        assert row["profile_independent_certificate"] is False
        assert row["row_sum_sup"] > 0.0
        assert row["column_sum_sup"] > 0.0
        assert row["schur_bound"] > 0.0
        assert "uniform_geometry_sweep" in row
        assert "worst_tail_mode" in row
        assert int(row["worst_tail_active_finite_k_count"]) > 0


def test_acl_schur_test_proof_supports_sampled_n_inverse_scale() -> None:
    payload, _text = run_script()
    stats = payload["n_times_schur_bound_stats"]
    fit = payload["fits"]["schur_bound_vs_N"]
    adv_stats = payload["adversarial_n_times_schur_bound_stats"]
    adv_fit = payload["fits"]["adversarial_schur_bound_vs_N"]

    assert stats["count"] == 4
    assert stats["relative_range"] < 0.1, stats
    assert fit["count"] == 4
    assert -1.05 < fit["log_log_slope"] < -0.8, fit
    assert adv_stats["count"] == 4
    assert adv_fit["count"] == 4


def test_acl_operator_norm_receipt_records_proof_artifact() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "ns_triad_kn_acl_schur_test_proof_20260624/summary.json" in text
    assert "ns_triad_kn_acl_schur_test_proof_20260624/summary.md" in text
    assert "canonicalSampledFiniteShellSchurTestWitness = record" in text
    assert "canonicalProfileIndependentSchurTestKernelSumBound = record" in text
    assert "mixedTailSchurTestKernelSumBound" not in text
    assert "postulate\n  mixedTailSchurTestKernelSumBound" not in text

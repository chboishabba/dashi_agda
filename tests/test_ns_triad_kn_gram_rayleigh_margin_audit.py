from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_gram_rayleigh_margin_audit.py"
DOC = REPO_ROOT / "docs" / "ns_triad_kn_369_high_high_gram_bridge.md"
BRIDGE_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKN369HighHighGramBridgeReceipt.agda"
)
AUDIT_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNGramRayleighMarginAuditReceipt.agda"
)


def _payload_from_stdout(stdout: str) -> dict:
    lines = [line for line in stdout.splitlines() if line.strip()]
    return json.loads(lines[-1])


def test_gram_rayleigh_margin_audit_runs() -> None:
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_gram_rayleigh_margin_audit"
    if out_dir.exists():
        for path in sorted(out_dir.rglob("*"), reverse=True):
            if path.is_file():
                path.unlink()
            elif path.is_dir():
                path.rmdir()
    result = subprocess.run(
        ["python", str(SCRIPT), "--output-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = _payload_from_stdout(result.stdout)
    assert payload["contract"] == "ns_triad_kn_gram_rayleigh_margin_audit"
    assert payload["fail_closed"] is True
    assert payload["candidate_only"] is True
    assert payload["sampled_schur_script_match"] is True
    assert payload["dangerous_cell_classification_closed"] is False
    assert len(payload["rows"]) == 4
    assert payload["log_entries"][0]["message"] == "started Gram Rayleigh-margin audit run"
    assert payload["log_entries"][-1]["message"] == "completed Gram Rayleigh-margin audit run"
    assert float(payload["elapsed_ms"]) >= 0.0
    for row in payload["rows"]:
        assert abs(row["lambda_min"] - row["rayleigh_quotient"]) < 1.0e-12
        assert row["diagonal_contribution"] > row["cross_offdiag_contribution"]
        assert row["diag_minus_cross"] > 0.0
        assert row["coherence_mu"] < 0.2
        assert row["support_size"] >= 2
        assert row["dominant_cell_classification"] == "open_from_receipts"
        assert row["verdict"] == "coercive_margin_plausible"
        assert row["dominant_negative_shell_pairs"]


def test_gram_bridge_doc_and_receipts_exist() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    doc_text = DOC.read_text(encoding="utf-8")
    assert "369 role:" in doc_text
    assert "369 non-role:" in doc_text
    assert "lambda_min(K_N(A)) >= c / N" in doc_text
    assert "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py" in doc_text

    assert BRIDGE_RECEIPT.is_file(), f"missing {BRIDGE_RECEIPT}"
    bridge_text = BRIDGE_RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKN369HighHighGramBridgeReceipt" in bridge_text
    assert "docs/ns_triad_kn_369_high_high_gram_bridge.md" in bridge_text
    assert "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py" in bridge_text
    assert "canonical369NonRoleRead" in bridge_text

    assert AUDIT_RECEIPT.is_file(), f"missing {AUDIT_RECEIPT}"
    audit_text = AUDIT_RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNGramRayleighMarginAuditReceipt" in audit_text
    assert "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py" in audit_text
    assert 'candidateOnly ≡ true' in audit_text
    assert 'theoremPromoted ≡ false' in audit_text

from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOC = REPO_ROOT / "docs" / "ns_triad_kn_cross_shell_schur_nullmode.md"
SUMMARY = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_cross_shell_schur_audit_20260626"
    / "schur_audit.json"
)


def test_schur_nullmode_doc_uses_candidate_only_language() -> None:
    text = DOC.read_text(encoding="utf-8")
    squashed = " ".join(text.split())
    assert "Proof target fixed" in text
    assert "supporting evidence" in text
    assert "No promotion claim made." in text
    assert "matrix-free `eigsh`" in text
    assert "Observed at N=6,8,10,12,14. Proof open." in text
    assert "constant-on-$C$" in text
    assert "symbolic null-mode identification" in squashed
    assert "factorization" in squashed
    assert "are still open." in squashed


def test_schur_audit_summary_records_matrix_free_receipt_flags() -> None:
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["candidate_only"] is True
    assert payload["theorem_promoted"] is False
    assert payload["gate1_closed"] is False
    assert payload["gate1_supported_at_tested_shells"] is True
    assert payload["schurComplementPsdVerified"] is True
    assert payload["schurComplementNullityOneObserved"] is True
    assert payload["schurComplementMatrixFreeAuditInstalled"] is True
    assert payload["schurComplementPsdProved"] is False
    assert payload["schurNullModeIdentified"] is False
    assert payload["schurNullModeFactorizationProved"] is False

    rows = {row["N"]: row for row in payload["rows"]}
    assert set(rows) == {12, 14}
    for shell in (12, 14):
        row = rows[shell]
        assert row["verdict"] == "schur_psd"
        assert row["S_C"]["evaluation_method"] == "eigsh"
        assert row["S_C"]["nullity_estimate"] == 1
        assert len(row["S_C"]["bottom_eigs"]) == 3

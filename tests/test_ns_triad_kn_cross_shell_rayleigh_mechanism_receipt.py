from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOC = REPO_ROOT / "docs" / "ns_triad_kn_cross_shell_rayleigh_mechanism.md"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNCrossShellRayleighMechanismReceipt.agda"
)
SUMMARY = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_gram_rayleigh_margin_audit_20260625"
    / "summary.json"
)


def test_cross_shell_rayleigh_doc_and_receipt_exist() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    text = DOC.read_text(encoding="utf-8")
    assert "low-high-high Gram coercivity at the high-high seam" in text
    assert "|k x p| / |k|^2 <= |p| / |k|" in text
    assert "1-(N-1)-N" in text
    assert "It does not prove the global theorem" in text

    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    receipt_text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNCrossShellRayleighMechanismReceipt" in receipt_text
    assert "docs/ns_triad_kn_cross_shell_rayleigh_mechanism.md" in receipt_text
    assert "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py" in receipt_text
    assert "candidateOnly ≡ true" in receipt_text
    assert "theoremPromoted ≡ false" in receipt_text


def test_cross_shell_rayleigh_doc_matches_sampled_support() -> None:
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    supports = [row["worst_eigenvector_support"] for row in payload["rows"]]
    assert supports == [[1, 6, 5], [8, 7, 1], [10, 9, 1], [12, 11, 1]]

    pair_heads = [row["dominant_negative_shell_pairs"][0]["shell_pair"] for row in payload["rows"]]
    assert pair_heads == ["1-6", "1-8", "1-10", "1-12"]

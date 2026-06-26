from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNExactOperatorFrontierReceipt.agda"
)
DOC = REPO_ROOT / "docs" / "ns_triad_kn_exact_operator_frontier.md"


def test_exact_operator_frontier_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNExactOperatorFrontierReceipt" in text
    assert "NSTriadKNPairIncidenceOperatorReceipt" in text
    assert "NSTriadKNMixedTailDiagonalResidueBridgeReceipt" in text
    assert "NSTriadKNMixedTailBKMProjectionSmallnessReceipt" in text
    assert '"q_gap(N) >= c_gap / N^2"' in text
    assert 'exactOperatorCanonicalized ≡ true' in text
    assert 'uniformProfileIndependentBoundClosed ≡ false' in text
    assert 'bkmResidenceBridgeClosed ≡ false' in text


def test_exact_operator_frontier_doc_exists() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    text = DOC.read_text(encoding="utf-8")
    assert "exact scripted mixed-tail cross block" in text
    assert "||L_FT,script^N||_op <= C / N" in text
    assert "SchurResidueScale" in text
    assert "BKM contradiction/exclusion route" in text

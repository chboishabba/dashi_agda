from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOC = REPO_ROOT / "docs" / "ns_triad_kn_gate2_seam_to_leakage_transfer.md"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNGate2SeamToLeakageTransferReceipt.agda"
)


def test_gate2_transfer_doc_exists() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    text = DOC.read_text(encoding="utf-8")
    assert "K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)" in text
    assert "Gate 2 is the transport step" in text
    assert "G2-A. Normalization agreement" in text
    assert "G2-B. Schur transport" in text
    assert "G2-C. Margin preservation" in text
    assert "G2-D. No missing outside-seam pollution" in text
    assert "normalizedGramToHelicalSchurAgreementProved = false" in text
    assert "gate2ConditionalTheoremProved = false" in text


def test_gate2_transfer_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNGate2SeamToLeakageTransferReceipt" in text
    assert "docs/ns_triad_kn_gate2_seam_to_leakage_transfer.md" in text
    assert "normalizedGramToHelicalSchurAgreementRecorded ≡ true" in text
    assert "seamCarrierMatchesLeakageLaneRecorded ≡ true" in text
    assert "gate2TransferSurfaceWritten ≡ true" in text
    assert "normalizedGramToHelicalSchurAgreementProved ≡ false" in text
    assert "schurCertificateTransfersToLeakageOperator ≡ false" in text
    assert "leakageTransferMarginPositive ≡ false" in text
    assert "outsideSeamNoPollutionProved ≡ false" in text
    assert "gate2ConditionalTheoremProved ≡ false" in text

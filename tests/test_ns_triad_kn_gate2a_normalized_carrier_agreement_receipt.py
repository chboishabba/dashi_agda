from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOC = REPO_ROOT / "docs" / "ns_triad_kn_gate2a_normalized_carrier_agreement.md"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNGate2ANormalizedCarrierAgreementReceipt.agda"
)


def test_gate2a_doc_exists() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    text = DOC.read_text(encoding="utf-8")
    assert "K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)" in text
    assert "V_Gram(N, A) = im(L_abs(A))" in text
    assert "V_Seam(N) = 1_C^perp" in text
    assert "The downstream lane starts from triad incidence data" in text
    assert "The upstream seam lane starts from the Schur complement" in text
    assert "J_N : V_Seam(N) -> V_Gram(N, A)" in text
    assert "J_N^abs" in text
    assert "J_N^neg" in text
    assert "x^T Schur(A_blk) x = (J_N^A x)^T A_blk (J_N^A x)" in text
    assert "gate2aOperatorSpecificSchurLiftsConstructed = true" in text
    assert "gate2aOperatorSpecificSchurLiftIdentitiesRecorded = true" in text
    assert "gate2aSchurSignSplitComparisonAuditInstalled = true" in text
    assert "Schur(L_abs)" in text
    assert "Schur(L_neg)" in text
    assert "0.168199" in text
    assert "gate2aDirectionalRatioStableObserved = true" in text
    assert "gate2aDirectionalRatioApproxOneSixthObserved = true" in text
    assert "gate2aCoarseTransportClosesObserved = false" in text
    assert "gate2aExtremizerAwareTransportProved = false" in text
    assert "normalizedGramToHelicalSchurAgreementProved = false" in text
    assert "gate2aCommonComparisonMapConstructed = false" in text
    assert "gate2aExactRestrictionIdentityObserved = false" in text
    assert "gate2aTwoSidedQuadraticFormBoundsProved = false" in text
    assert "gate2aConditionalLemmaProved = false" in text


def test_gate2a_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNGate2ANormalizedCarrierAgreementReceipt" in text
    assert "docs/ns_triad_kn_gate2a_normalized_carrier_agreement.md" in text
    assert "gate2aCarrierSpacesIdentified ≡ true" in text
    assert "gate2aNormalizationMismatchIdentified ≡ true" in text
    assert "gate2aComparisonMapWritten ≡ true" in text
    assert "gate2aOperatorSpecificSchurLiftsConstructed ≡ true" in text
    assert "gate2aOperatorSpecificSchurLiftIdentitiesRecorded ≡ true" in text
    assert "gate2aSchurSignSplitComparisonAuditInstalled ≡ true" in text
    assert "gate2aDirectionalRatioStableObserved ≡ true" in text
    assert "gate2aDirectionalRatioApproxOneSixthObserved ≡ true" in text
    assert "gate2aCoarseTransportClosesObserved ≡ false" in text
    assert "normalizedGramToHelicalSchurAgreementProved ≡ false" in text
    assert "gate2aCommonComparisonMapConstructed ≡ false" in text
    assert "schurSeamCarrierEmbedsIntoGramCarrier ≡ false" in text
    assert "gramSeamQuadraticFormMatchProved ≡ false" in text
    assert "gate2aExactRestrictionIdentityObserved ≡ false" in text
    assert "gate2aTwoSidedQuadraticFormBoundsProved ≡ false" in text
    assert "gate2aExtremizerAwareTransportProved ≡ false" in text
    assert "gate2aConditionalLemmaProved ≡ false" in text

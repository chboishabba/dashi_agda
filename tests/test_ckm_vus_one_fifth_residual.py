from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "CKMVusCarrierPredictionTargetReceipt.agda"
)


@pytest.fixture(scope="module")
def receipt_text() -> str:
    return RECEIPT.read_text(encoding="utf-8")


def block_between(text: str, start: str, end: str) -> str:
    match = re.search(
        rf"{re.escape(start)}(?P<body>.*?){re.escape(end)}",
        text,
        flags=re.DOTALL,
    )
    assert match is not None, f"missing block from {start!r} to {end!r}"
    return match.group("body")


def field_is_false(record_block: str, field_name: str) -> bool:
    return (
        re.search(
            rf";\s*{re.escape(field_name)}\s*=\s*false\b",
            record_block,
            flags=re.DOTALL,
        )
        is not None
    )


def test_ckm_vus_receipt_contains_one_fifth_pdg_residual_law(
    receipt_text: str,
) -> None:
    for term in (
        "record CKMVusOneFifthPdgApproxResidualLaw",
        "canonicalCKMVusOneFifthPdgApproxResidualLaw",
        "oneFifthToPdgApproxResidualLaw",
        "oneFifthToPdgApproxResidualLawIsCanonical",
        "oneFifthToPdgApproxResidualLawSocketValue",
        "oneFifthToPdgApproxResidualLawTargetDatum",
    ):
        assert term in receipt_text, term


def test_ckm_vus_one_fifth_residual_records_exact_one_fortieth_facts(
    receipt_text: str,
) -> None:
    for term in (
        "pdgApproxVusReducedSignedDatum",
        "Matter.mixingSignedRationalDatum 9 40 true",
        "vusOneFifthToPdgApproxAbsoluteGapSignedDatum",
        "Matter.mixingSignedRationalDatum 1 40 true",
        "absoluteGapIsOneFortieth",
        "absoluteGapReducesFromCommonDenominator",
        "oneFifthToPdgApproxResidualLawGapIsOneFortieth",
        "absolute gap 1/40",
    ):
        assert term in receipt_text, term

    residual_law = block_between(
        receipt_text,
        "canonicalCKMVusOneFifthPdgApproxResidualLaw =",
        "data AcceptedExactPhysicalVusMatch",
    )
    for term in (
        "; pdgApproxVusReduced =\n        pdgApproxVusReducedGaussianDatum",
        "; absoluteGap =\n        vusOneFifthToPdgApproxAbsoluteGapGaussianDatum",
        "; commonDenominator =\n        200",
        "; cabibboLikeScaledNumerator =\n        40",
        "; pdgApproxScaledNumerator =\n        45",
        "; absoluteGapScaledNumerator =\n        5",
    ):
        assert term in residual_law, term


def test_ckm_vus_residual_keeps_pdg_and_physical_ckm_promotion_false(
    receipt_text: str,
) -> None:
    residual_law = block_between(
        receipt_text,
        "canonicalCKMVusOneFifthPdgApproxResidualLaw =",
        "data AcceptedExactPhysicalVusMatch",
    )
    receipt = block_between(
        receipt_text,
        "canonicalCKMVusCarrierPredictionTargetReceipt =",
        "ckmVusCarrierTargetRecordsNonIdentityTarget",
    )

    for field_name in (
        "exactPDGMatchClaimed",
        "physicalCKMPromotionConstructed",
    ):
        assert field_is_false(residual_law, field_name), field_name

    for field_name in (
        "cabibboLikeTransportExactPDGMatchClaimedIsFalse",
        "cabibboLikeTransportPhysicalPromotionIsFalse",
        "oneFifthToPdgApproxResidualLawExactPDGMatchIsFalse",
        "oneFifthToPdgApproxResidualLawPhysicalPromotionIsFalse",
        "exactPhysicalMatchClaimed",
        "physicalCKMPromotionConstructed",
    ):
        assert field_name in receipt, field_name

    assert field_is_false(receipt, "exactPhysicalMatchClaimed")
    assert field_is_false(receipt, "physicalCKMPromotionConstructed")

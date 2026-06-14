from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
W4_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "W4MatterStressEnergyInterfaceReceipt.agda"
)


def read_w4_receipt() -> str:
    assert W4_RECEIPT.is_file(), f"missing {W4_RECEIPT.relative_to(REPO_ROOT)}"
    return W4_RECEIPT.read_text(encoding="utf-8", errors="replace")


def block_between(text: str, start: str, end: str) -> str:
    start_index = text.index(start)
    end_index = text.index(end, start_index)
    return text[start_index:end_index]


def field_assigned_false(block: str, field_name: str) -> bool:
    return bool(re.search(rf";\s*{re.escape(field_name)}\s*=\s*false\b", block))


def test_w4_gate4_zero_source_receipt_consumes_det_canonical_law() -> None:
    text = read_w4_receipt()

    record_block = block_between(
        text,
        "record W4Gate4ZeroSourceCompatibilityReceipt : Setω where",
        "canonicalW4Gate4ZeroSourceCompatibilityReceipt :",
    )
    canonical_block = block_between(
        text,
        "canonicalW4Gate4ZeroSourceCompatibilityReceipt =",
        "w4Gate4ZeroSourceCompatibilityAllLaneLawCanonical :",
    )

    assert "allLaneEinsteinTensorLaw :" in record_block
    assert "DET.FactorVecSSPAllLaneContractionEinsteinTensorLaw" in record_block
    assert "allLaneEinsteinTensorLawIsDETCanonical :" in record_block
    assert (
        "DET.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw"
        in record_block
    )

    assert (
        re.search(
            r";\s*allLaneEinsteinTensorLaw\s*=\s*"
            r"DET\.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw\b",
            canonical_block,
        )
        is not None
    )
    assert "; allLaneEinsteinTensorLawIsDETCanonical =" in canonical_block
    assert "refl" in canonical_block


def test_w4_gate4_zero_source_receipt_proves_pointwise_einstein_tensor_zero() -> None:
    text = read_w4_receipt()
    record_block = block_between(
        text,
        "record W4Gate4ZeroSourceCompatibilityReceipt : Setω where",
        "canonicalW4Gate4ZeroSourceCompatibilityReceipt :",
    )
    canonical_block = block_between(
        text,
        "canonicalW4Gate4ZeroSourceCompatibilityReceipt =",
        "w4Gate4ZeroSourceCompatibilityAllLaneLawCanonical :",
    )

    expected_type = (
        r"einsteinTensorZeroSourceCompatibility\s*:\s*"
        r"\(base\s*:\s*GL\.FactorVec\)\s*→\s*"
        r"\(mu\s+nu\s*:\s*SSP\)\s*→\s*"
        r"DET\.factorVecSSPEinsteinTensor\s+base\s+mu\s+nu\s*"
        r"≡\s*DET\.zeroFactorVec"
    )
    assert re.search(expected_type, record_block) is not None

    assert (
        "DET.FactorVecSSPAllLaneContractionEinsteinTensorLaw.einsteinTensorZeroTableLaw"
        in canonical_block
    )
    assert (
        "DET.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw"
        in canonical_block
    )


def test_w4_gate4_zero_source_receipt_keeps_promotions_false() -> None:
    text = read_w4_receipt()
    record_block = block_between(
        text,
        "record W4Gate4ZeroSourceCompatibilityReceipt : Setω where",
        "canonicalW4Gate4ZeroSourceCompatibilityReceipt :",
    )
    canonical_block = block_between(
        text,
        "canonicalW4Gate4ZeroSourceCompatibilityReceipt =",
        "w4Gate4ZeroSourceCompatibilityAllLaneLawCanonical :",
    )
    proof_block = block_between(
        text,
        "w4Gate4ZeroSourceCompatibilityNoSourcedPromotion :",
        "w4Gate4ZeroSourceCompatibilityNoCandidate256Promotion =",
    )

    for field_name in ("selectedNonFlatEquationPromoted", "candidate256Promoted"):
        assert f"{field_name} :" in record_block
        assert f"{field_name}IsFalse :" in record_block
        assert f"{field_name}\n      ≡\n      false" in record_block
        assert field_assigned_false(canonical_block, field_name)

    assert (
        "W4Gate4ZeroSourceCompatibilityReceipt.selectedNonFlatEquationPromoted"
        in proof_block
    )
    assert "w4Gate4ZeroSourceCompatibilityNoSourcedPromotion =" in proof_block
    assert (
        "W4Gate4ZeroSourceCompatibilityReceipt.candidate256Promoted" in text
    )
    assert "w4Gate4ZeroSourceCompatibilityNoCandidate256Promotion =" in text

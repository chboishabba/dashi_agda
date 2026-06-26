from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
NUMERIC_VALIDATOR = ROOT / "DASHI" / "Promotion" / "NumericAuthorityPayloadValidator.agda"
W4_EXTERNAL = (
    ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "W4PhysicalCalibrationExternalReceiptObligation.agda"
)
W4_REQUEST = (
    ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "W4PhysicalCalibrationExternalReceiptRequestPack.agda"
)


def test_numeric_payload_shape_validator_requires_dimension_and_factorization_payloads() -> None:
    text = NUMERIC_VALIDATOR.read_text(encoding="utf-8")

    assert "record SIBaseDimensionVector" in text
    assert "record ExternalPayloadShapeRequirement" in text
    assert "missingDimensionVectorCarrierField" in text
    assert "missingDimensionVectorWitnessField" in text
    assert "missingUnitFactorizationReceiptField" in text
    assert "canonicalExternalShapePayloadFields" in text
    assert "externalShapePayloadFieldCountIs3" in text
    assert "canonicalExternalPayloadShapeRequirements" in text


def test_numeric_payload_shape_validator_remains_fail_closed() -> None:
    text = NUMERIC_VALIDATOR.read_text(encoding="utf-8")

    assert "dimensionVectorCarrierPresent = false" in text
    assert "dimensionVectorWitnessPresent = false" in text
    assert "unitFactorizationReceiptPresent = false" in text
    assert "acceptedAuthorityTokenPresent = false" in text
    assert "numericValueLoaded = false" in text
    assert "allExternalShapeRequirementsMissingPayload = true" in text
    assert "numericValuePromoted = false" in text


def test_w4_external_receipt_shape_has_dimension_vector_and_factorization_checker() -> None:
    text = W4_EXTERNAL.read_text(encoding="utf-8")
    request_text = W4_REQUEST.read_text(encoding="utf-8")

    assert "record Candidate256PhysicalCalibrationDimensionVector" in text
    assert "record Candidate256PhysicalCalibrationFactorizationChecker" in text
    assert "physicalDimensionVector :" in text
    assert "missingExternalPhysicalDimensionVector" in text
    assert "∷ missingExternalPhysicalDimensionVector" in text
    assert "dimensionVectorBoundary : String" in text
    assert "physicalDimensionVector : structured SI-base exponent vector" in request_text
    assert "Do not replace the dimension vector with prose unit labels" in request_text


def test_w4_external_receipt_still_has_no_local_authority_constructor() -> None:
    text = W4_EXTERNAL.read_text(encoding="utf-8")

    assert "Candidate256PhysicalCalibrationAuthorityToken →\n  ⊥" in text
    assert "candidate256PhysicalCalibrationAuthorityTokenImpossibleHere ()" in text
    assert "This module does not construct Candidate256PhysicalCalibrationAuthorityToken" in text
    assert "physicalCalibrationPromoted =\n        false" in text

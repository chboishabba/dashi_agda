from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI = REPO_ROOT / "DASHI"
ROLLUP = DASHI / "Physics" / "Closure" / "YeRedshiftEverything.agda"

EXPECTED = {
    "DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact":
        DASHI / "Physics" / "Closure" / "BothwellYe2022PublishedGradientPayloadExact.agda",
    "DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact":
        DASHI / "Physics" / "Closure" / "BothwellYe2022RedshiftComparisonExact.agda",
    "DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftIngestionStatusExact":
        DASHI / "Physics" / "Closure" / "QuantumClockEmpiricalRedshiftIngestionStatusExact.agda",
}


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_bothwell_ye_published_payload_materialises_literal_source_numbers() -> None:
    text = read(EXPECTED["DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact"])
    for literal in (
        "-1.09e-19 mm^-1",
        "-1.00(12)e-19 mm^-1",
        "-9.8(2.3)e-20 mm^-1",
        "-1.28(27)e-19 mm^-1",
        "-9.796 m s^-2",
        "6.04 um",
        "0.11(0.06) degrees",
        "3e-21 mm^-1",
        "1.7e-20 mm^-1",
        "-5e-21 mm^-1",
        "1e-21 mm^-1",
    ):
        assert literal in text

    assert "publicRawDataAvailable = false" in text
    assert "publicAnalysisCodeAvailable = false" in text
    assert "availableFromCorrespondingAuthorsOnReasonableRequest = true" in text
    assert "sourceArtifactSha256Present = false" in text


def test_redshift_comparison_is_same_scale_and_within_published_uncertainty() -> None:
    text = read(EXPECTED["DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact"])
    for name in (
        "publishedPredictedMagnitudeUnits = 109",
        "publishedCorrectedObservedMagnitudeUnits = 98",
        "publishedCorrectedObservedUncertaintyUnits = 23",
        "publishedCorrectedAbsoluteResidualUnits = 11",
        "publishedSynchronousObservedMagnitudeUnits = 128",
        "publishedSynchronousObservedUncertaintyUnits = 27",
        "publishedSynchronousAbsoluteResidualUnits = 19",
        "canonicalPublishedCorrectedWithinOneQuotedUncertainty",
        "canonicalPublishedSynchronousWithinOneQuotedUncertainty",
        "gravityFormulaReference",
        "speedOfLightExactSIReference",
        "ghOverCSquaredScaledExact",
        "canonicalLowerRoundingBoundHolds",
        "canonicalUpperRoundingBoundHolds",
    ):
        assert name in text

    assert "comparisonProvesGeneralRelativity = false" in text
    assert "comparisonUsesRawUnpublishedData = false" in text


def test_ingestion_status_reconciles_partial_source_ingestion_without_terminal_promotion() -> None:
    text = read(EXPECTED["DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftIngestionStatusExact"])
    for marker in (
        "experimentIdentified = true",
        "publicationMetadataIngested = true",
        "publishedNumericPayloadIngested = true",
        "publishedSystematicsSummaryIngested = true",
        "sameScaleComparisonConstructed = true",
        "publicRawDataIngested = false",
        "artifactChecksumIngested = false",
        "fullCovarianceIngested = false",
        "genericAcceptanceTokenConstructed = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in text


def test_new_owners_are_exposed_once_by_focused_rollup() -> None:
    rollup = read(ROLLUP)
    for module in EXPECTED:
        line = f"import {module}"
        assert rollup.count(line) == 1, f"expected exactly one import: {line}"

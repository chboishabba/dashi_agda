from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI = REPO_ROOT / "DASHI"
MODULE = DASHI / "Physics" / "Closure" / "BothwellYe2022PublicArtifactLocatorExact.agda"
STATUS = DASHI / "Physics" / "Closure" / "QuantumClockEmpiricalRedshiftIngestionStatusExact.agda"
ROLLUP = DASHI / "Physics" / "Closure" / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_public_artifact_locator_pays_identity_and_access_date_without_inventing_checksum() -> None:
    text = read(MODULE)
    for marker in (
        "10.1038/s41586-021-04349-7",
        "https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=933368",
        "https://www.nist.gov/publications/resolving-gravitational-redshift-across-millimetre-scale-atomic-sample",
        "2026-10-12",
        "experimentArtifactIdentityIngested = true",
        "sourceAccessDateIngested = true",
        "experimentArtifactByteChecksumIngested = false",
        "rawExperimentArraysInArtifact = false",
        "analysisCodeInArtifact = false",
    ):
        assert marker in text


def test_locator_keeps_publication_artifact_distinct_from_raw_data_and_code() -> None:
    text = read(MODULE)
    for marker in (
        "publicationArtifactIsRawExperimentDataset = false",
        "publicationArtifactIsAnalysisCodeBundle = false",
        "locatorDischargesGenericAcceptanceToken = false",
    ):
        assert marker in text


def test_status_records_locator_paid_but_checksum_and_terminal_gates_closed() -> None:
    text = read(STATUS)
    for marker in (
        "experimentArtifactIdentityIngested = true",
        "experimentSourceAccessDateIngested = true",
        "experimentPaperArtifactChecksumIngested = false",
        "genericAcceptanceTokenConstructed = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in text


def test_rollup_imports_public_artifact_locator_once() -> None:
    rollup = read(ROLLUP)
    line = "import DASHI.Physics.Closure.BothwellYe2022PublicArtifactLocatorExact"
    assert rollup.count(line) == 1

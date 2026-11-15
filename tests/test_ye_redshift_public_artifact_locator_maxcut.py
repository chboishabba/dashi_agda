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
        "https://jila.colorado.edu/sites/default/files/2022-02/Redshift%201%20mm_Nature%202022.pdf",
        "https://eprints.gla.ac.uk/264685/2/264685.pdf",
        "2026-10-16",
        "experimentArtifactIdentityIngested = true",
        "redundantPublicLocatorIngested = true",
        "sourceAccessDateIngested = true",
        "experimentArtifactByteChecksumIngested = false",
        "rawExperimentArraysInArtifact = false",
        "analysisCodeInArtifact = false",
    ):
        assert marker in text


def test_locator_distinguishes_version_of_record_from_accepted_manuscript() -> None:
    text = read(MODULE)
    for marker in (
        "jilaMirrorRole = \"public PDF mirror of the Nature article\"",
        "glasgowMirrorRole = \"author accepted manuscript; not asserted byte-identical to version of record\"",
        "publicMirrorsAssertedByteIdentical = false",
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

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_100k_release_owner_separates_published_acquisition_from_archive_log():
    text = (ROOT / "DASHI/Physics/Optics/BerkeleyPLD100kReleaseProvenanceExact.agda").read_text(encoding="utf-8")
    for marker in [
        "10.1364/OE.608614",
        "firstHundredThousandMIRFLICKRImagesPaid = true",
        "publishedSynchronizedThreeCameraAcquisitionPaid = true",
        "publishedInterCameraDelayMs = 200",
        "publishedInterImageDelayMs = 500",
        "publishedRMLExposureMs = 80",
        "publishedDiffuserExposureMs = 50",
        "publishedLensExposureMs = 4",
        "published100kAcquisitionProvenancePaid = true",
        "published100kExposureIdentityPaid = true",
        "exactArchiveRunLogRecovered = false",
        "exactArchiveExposureSameRunPaid = false",
    ]:
        assert marker in text


def test_maxcut_pays_published_dataset_provenance_but_not_archive_run_log():
    text = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text(encoding="utf-8")
    assert "published100kAcquisitionProvenancePinned = true" in text
    assert "published100kExposureIdentityPinned = true" in text
    assert "exactArchiveExposureSameRunPaid = Release100k.exactArchiveExposureSameRunPaid" in text

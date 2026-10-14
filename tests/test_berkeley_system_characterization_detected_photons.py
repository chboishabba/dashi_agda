from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_real_system_characterization_receipt_is_pinned_and_non_promoting():
    owner = ROOT / "DASHI/Physics/Optics/BerkeleySystemCharacterizationDetectedPhotonExact.agda"
    text = owner.read_text(encoding="utf-8")
    for marker in [
        "1nr1pUrg80JQm8WyLa6wvFktmJ_pniOio",
        "1mHJp99Twe0nSL3_HbNXjXjmV9zDy3YvI",
        "1-0rpd6gHgjdFshVMl6Gw1M0NqAliechM",
        "matchedCharacterizationPositions = 15",
        "realMeasuredTIFFsExecuted = true",
        "detectedPhotonCharacterizationPaid = true",
        "characterizationExposureMetadataRecovered = false",
        "exposureNormalizedResponsePaid = false",
        "incidentThroughputPaid = false",
        "matchedIncidentPhotonBudgetPaid = false",
    ]:
        assert marker in text


def test_real_characterization_receipt_and_script_are_exported():
    assert (ROOT / "receipts/optics/berkeley_system_characterization_detected_photon_receipt.json").exists()
    script = (ROOT / "scripts/check_berkeley_system_characterization_detected_photons.py").read_text(encoding="utf-8")
    assert "clip((digital - intercept) / slope, 0, infinity)" in script
    rollup = (ROOT / "DASHI/Physics/Optics/Everything.agda").read_text(encoding="utf-8")
    assert "BerkeleySystemCharacterizationDetectedPhotonExact" in rollup
    maxcut = (ROOT / "DASHI/Physics/Optics/Diffraction3DImagingAcquisitionMaxCutExact.agda").read_text(encoding="utf-8")
    assert "realSystemCharacterizationDetectedPhotonReceiptCaptured" in maxcut

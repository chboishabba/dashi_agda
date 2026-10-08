from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Physics/Optics/FresnelAngularSpectrumPropagationExact.agda": [
        "record FresnelPropagationReceipt",
        "record AngularSpectrumPropagationReceipt",
        "fresnelAngularSpectrumSameField",
    ],
    "DASHI/Physics/Optics/DiffuserPhysicalForwardWeldExact.agda": [
        "record PhysicalDiffuserForwardWeld",
        "cameraModel",
        "encodeIsPhysicalIntensity",
        "depthPSFIsPhysical",
    ],
    "DASHI/Physics/Optics/DiffuserRestrictedStabilityProducerExact.agda": [
        "record RestrictedSeparationProducer",
        "sameEncoder",
        "toRestrictedInverseBudget",
    ],
    "DASHI/Physics/Optics/PhotonDetectorChannelExact.agda": [
        "record PhotonDetectorChannel",
        "expectedCounts",
        "fullWell",
        "quantise",
        "recordedObservation",
    ],
    "DASHI/Physics/Optics/DiffuserInformationDesignExact.agda": [
        "record ImagingDesignObjective",
        "samePhysicalChannel",
        "consumerRisk",
        "mutualInformationObjective",
    ],
    "DASHI/Physics/Optics/MatchedPhotonImagerComparatorExact.agda": [
        "data ImagerFamily",
        "focusedLens",
        "randomDiffuser",
        "fresnelZonePlate",
        "record MatchedPhotonComparator",
        "samePhotonBudget",
        "samePixelBudget",
        "sameSceneFamily",
    ],
    "DASHI/Physics/Optics/Diffraction3DImagingPhysicalMaxCutExact.agda": [
        "record Diffraction3DImagingPhysicalMaxCut",
        "propagationPaid",
        "physicalWeldPaid",
        "restrictedStabilityPaid",
        "detectorChannelPaid",
        "informationDesignPaid",
        "matchedPhotonComparatorPaid",
    ],
}


def test_required_owners_and_same_object_markers_exist():
    for rel, markers in REQUIRED.items():
        path = ROOT / rel
        assert path.exists(), f"missing max-cut owner: {rel}"
        text = path.read_text(encoding="utf-8")
        for marker in markers:
            assert marker in text, f"{rel} missing marker {marker!r}"


def test_maxcut_reuses_existing_diffuser_stability_and_observer_owners():
    path = ROOT / "DASHI/Physics/Optics/Diffraction3DImagingPhysicalMaxCutExact.agda"
    text = path.read_text(encoding="utf-8")
    for owner in (
        "DiffuserImagingObserverDynamicRangeExact",
        "DiffuserNoiseStableRecoveryExact",
        "HyperformObserverFactorisationExact",
        "FresnelZonePlateDiffuserCodecBridgeExact",
    ):
        assert owner in text


def test_rollup_exports_physical_maxcut():
    candidates = [
        ROOT / "DASHI/Physics/Optics/Everything.agda",
        ROOT / "DASHI/Physics/Everything.agda",
        ROOT / "DASHI/Everything.agda",
    ]
    existing = [p for p in candidates if p.exists()]
    assert existing, "no optics/physics rollup found"
    assert any(
        "Diffraction3DImagingPhysicalMaxCutExact" in p.read_text(encoding="utf-8")
        for p in existing
    ), "physical max-cut is not exported from any existing rollup"

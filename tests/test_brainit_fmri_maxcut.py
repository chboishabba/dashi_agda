from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = {
    "DASHI/Biology/BrainITSourceBoundaryExact.agda": [
        "module DASHI.Biology.BrainITSourceBoundaryExact where",
        "brainITArxiv251025976",
        "universalEncoderArxiv240612179",
        "arbitraryThoughtReadingSupportedIsFalse",
        "remotePointAtPersonReadingSupportedIsFalse",
    ],
    "DASHI/Biology/BrainITFunctionalClusterTransferExact.agda": [
        "module DASHI.Biology.BrainITFunctionalClusterTransferExact where",
        "reportedVoxelCount = 40000",
        "reportedFunctionalClusterCount = 128",
        "sharedClusterWeights",
        "oneHourTransferComparableToFortyHourBaseline",
    ],
    "DASHI/Biology/BrainITObservationPromotionBoundaryExact.agda": [
        "module DASHI.Biology.BrainITObservationPromotionBoundaryExact where",
        "coarseObservationCollisionReused",
        "reconstructionDoesNotRecoverMicroscopicState",
        "viewedImageReconstructionDoesNotImplyArbitraryThoughtReading",
        "nonInvasiveDoesNotImplyRemoteReadout",
    ],
    "DASHI/Biology/BrainITValidation.agda": [
        "module DASHI.Biology.BrainITValidation where",
        "brainITMaxCutPinsSourceBoundary",
        "brainITMaxCutPinsObservationFirewall",
    ],
}


def test_brainit_maxcut_surface_exists():
    missing = []
    for rel, markers in required.items():
        p = ROOT / rel
        if not p.exists():
            missing.append(f"missing file: {rel}")
            continue
        text = p.read_text()
        for marker in markers:
            if marker not in text:
                missing.append(f"{rel}: missing marker {marker!r}")
    assert not missing, "\n".join(missing)

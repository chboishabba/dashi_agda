from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
EXOTIC = REPO_ROOT / "DASHI" / "Physics" / "ExoticGravity"
EVERYTHING = EXOTIC / "Everything.agda"

EXPECTED = {
    "AntigravitySearchNonGeometricOppositeExact.agda": (
        "couplingSignFlipConstructsGeometricOppositeMetric",
        "fixedMetricSignedCouplingRelabelIsPhysicalAntipode",
        "argumentResponseDonorBoundary",
    ),
    "WeightMetricApparentMassExact.agda": (
        "weightChangeImpliesMetricChange",
        "metricChangeCanAlterWeightGivenSupportModel",
        "apparentMassIsNotDefinitionallyInertialMass",
        "apparentMassIsNotDefinitionallyPassiveGravitationalResponse",
        "rationalWeight",
        "apparentMassFromSupportForce",
        "sameMetricSupportAccelerationChangesWeight",
    ),
    "AntigravityDeviceOpticalMetricDiscriminatorExact.agda": (
        "deviceStateToStressEnergy",
        "ordinaryMetricPrediction",
        "candidateMetricPrediction",
        "opticalMetricReadout",
        "samePhysicalDeviceState",
        "crossChannelConsistency",
        "candidateResidualBetterThanOrdinaryResidual",
        "DeviceModulationExperiment",
        "modulationLockInReceipt",
        "positiveGActiveStressRoute",
        "existingLocalizedPositiveGRepulsiveShell",
        "existingLiTorrKernel",
        "existingSchutzholdTerminalFrontier",
    ),
}


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_modules_exist_and_expose_contracts() -> None:
    for filename, required in EXPECTED.items():
        text = read(EXOTIC / filename)
        for token in required:
            assert token in text, f"{filename} missing contract token {token}"


def test_opposite_search_firewall_is_fail_closed() -> None:
    text = read(EXOTIC / "AntigravitySearchNonGeometricOppositeExact.agda")
    assert "false false false" in text or "false\n    false\n    false" in text
    assert "geometricOppositeRequiresSolvedGeometryReceipt" in text


def test_negative_g_scope_search_consumes_non_geometric_opposite_firewall() -> None:
    text = read(EXOTIC / "AntigravityNegativeGCouplingScopeProofSearchExact.agda")
    assert "AntigravitySearchNonGeometricOppositeExact as NonGeometric" in text
    assert "existingNonGeometricOppositeBoundary" in text
    assert "NegativeGGeometricPromotionGate" in text
    assert "geometricOppositeReceipt" in text
    assert "geometricOppositeRequiresSolvedGeometryReceipt" in read(
        EXOTIC / "AntigravitySearchNonGeometricOppositeExact.agda"
    )


def test_weight_and_metric_are_not_conflated() -> None:
    text = read(EXOTIC / "WeightMetricApparentMassExact.agda")
    assert "weightChangeImpliesMetricChange : Bool" in text
    assert "weightChangeImpliesMetricChangeIsFalse" in text
    assert "metricChangeCanAlterWeightGivenSupportModel : Bool" in text
    assert "metricChangeCanAlterWeightGivenSupportModelIsTrue" in text
    assert "support-force observable" in text
    assert "sameMetricSupportAccelerationChangesWeight" in text


def test_device_discriminator_requires_same_object_and_cross_channel_checks() -> None:
    text = read(EXOTIC / "AntigravityDeviceOpticalMetricDiscriminatorExact.agda")
    for token in (
        "samePhysicalDeviceState",
        "sameOpticalProbe",
        "sameCalibration",
        "weightChannel",
        "freeFallChannel",
        "clockChannel",
        "opticalPhaseChannel",
        "reversalRepresentation",
        "modulationLockInReceipt",
        "positiveGActiveStressRoute",
        "existingSchutzholdTerminalFrontier",
    ):
        assert token in text


def test_everything_imports_new_modules() -> None:
    text = read(EVERYTHING)
    for filename in EXPECTED:
        module = "DASHI.Physics.ExoticGravity." + filename.removesuffix(".agda")
        assert f"import {module}" in text

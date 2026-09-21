from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
BIOLOGY = REPO_ROOT / "DASHI" / "Biology"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

EXPECTED = {
    "AvianMagneticFieldPerturbationReceipt.agda": (
        "noPerturbationToReceptorIdentityClaim",
        "noRFDisruptionToQuantumMechanismProof",
        "receptorMechanismIdentifiedByPerturbationIsFalse",
    ),
    "AvianMagneticPerturbationSourceRegistry.agda": (
        "wiltschkoWiltschko1972",
        "10.1126/science.176.4030.62",
        "engelsEtAl2014",
        "10.1038/nature13290",
        "receptorMechanismEstablished",
    ),
    "AvianRFOverlayMechanismAdapter.agda": (
        "legacyRouteIsCryptochromeSpecificIsTrue",
        "legacyRouteIsMechanismNeutralIsFalse",
        "genericRFDisruptionProvesRadicalPairMechanismIsFalse",
    ),
    "AvianMagnetoreceptionRFGoniometerPhasedArrayBridge.agda": (
        "canonicalGoniometerRoleFirewall",
        "canonicalSteeringDFFirewall",
        "canonicalCrossDomainAuthorityFirewall",
        "coilSystemIsPhasedArrayIsFalse",
        "goniometerIsBirdExperimentApparatusIsFalse",
        "apparatusIdentifiesBiologicalMechanismIsFalse",
        "exactFieldAtReceptorRecoveredIsFalse",
    ),
}


def test_magnetic_perturbation_rf_geometry_tranche() -> None:
    for filename, tokens in EXPECTED.items():
        text = (BIOLOGY / filename).read_text(encoding="utf-8")
        for token in tokens:
            assert token in text, (filename, token)


def test_everything_wires_magnetic_perturbation_rf_geometry_tranche() -> None:
    text = EVERYTHING.read_text(encoding="utf-8")
    for filename in EXPECTED:
        module = filename.removesuffix(".agda")
        assert f"import DASHI.Biology.{module}" in text

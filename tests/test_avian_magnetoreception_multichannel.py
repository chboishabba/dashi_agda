from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
BIOLOGY = REPO_ROOT / "DASHI" / "Biology"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

MODULES = {
    "MagnetoreceptionSurface.agda": (
        "noSingleMechanismExclusivityClaim",
        "noReceptorToBrainClosureClaim",
        "noIronPresenceToMagnetoreceptorPromotion",
    ),
    "AvianCryptochromeMagnetoreceptionInhabitant.agda": (
        "radicalPairRetinalChannel",
        "cryptochromeMechanismExclusiveIsFalse",
        "visualOverlayUniversalIsFalse",
    ),
    "AvianMagnetoreceptionSourceRegistry.agda": (
        "lisowskiEtAl2026",
        "10.1126/science.ady2486",
        "directNeuralTransductionEstablished",
    ),
    "AvianHepaticMacrophageMagnetoreception.agda": (
        "depletionDisruptsOvercastOrientationIsTrue",
        "visibleSunControlRetainsOrientationIsTrue",
        "afferentMechanismDirectlyEstablishedIsFalse",
        "sourceReceiptIsLisowski2026",
    ),
    "AvianMagnetoreceptionCueFusion.agda": (
        "overcastDepletionChangesPolicy",
        "solarCueSubstitutesAcrossMacrophageState",
        "fullSensorFusionRecoveredIsFalse",
    ),
    "AvianMagnetoreceptionCrossScaleBridge.agda": (
        "canonicalNeurochemicalAtomicChemistryBridge",
        "canonicalFerritinophagyLogic",
        "canonicalProteinHormoneChemistryCellBridge",
        "canonicalCellDifferentiationCommunicationBridge",
        "canonicalEmbodiedMotorMultisensoryBridge",
        "canonicalNeurochemicalTransmissionBridge",
        "brainVocabularySurface",
        "atomicToBehaviorDerivationClaimIsFalse",
    ),
    "AvianMagnetoreceptionHardProblemResidualV2.agda": (
        "afferentNeuralRepresentation",
        "multisensoryCueIntegration",
        "phenomenalContentGap",
        "phenomenalContentRecoveredIsFalse",
        "retinalBranchRequiredIsFalse",
        "hepaticBranchExclusiveIsFalse",
    ),
}


def test_multichannel_magnetoreception_modules_exist_and_keep_boundaries() -> None:
    for filename, tokens in MODULES.items():
        path = BIOLOGY / filename
        assert path.exists(), filename
        text = path.read_text(encoding="utf-8")
        for token in tokens:
            assert token in text, (filename, token)


def test_everything_wires_multichannel_magnetoreception_tranche() -> None:
    text = EVERYTHING.read_text(encoding="utf-8")
    for filename in MODULES:
        module = filename.removesuffix(".agda")
        assert f"import DASHI.Biology.{module}" in text

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_birthmark_continuum_round4_registered():
    expected = {
        "DASHI/Quantum/QuantumBirthmarkTiltedWallStaticNoGoExact.agda": [
            "vacuumEnergyGapIsThreeSixtyFourths",
            "staticPlanarWallEqualVacuumEnergyRequired",
            "selectedTiltedPotentialStaticWallNoGo",
            "movingOrCurvedWallStillAllowed",
        ],
        "DASHI/Quantum/QuantumBirthmarkHorizonThermalCriticalScalingExact.agda": [
            "horizonThermalCoefficientIsThreeEighths",
            "horizonThermalHubbleExponentIsTwo",
            "historyFractionEqualsCriticalFraction",
            "historyFractionStillMicroscopicInput",
        ],
        "DASHI/Quantum/QuantumBirthmarkClosedDeSitterBouncePhaseCurveExact.agda": [
            "closedFriedmannConstraint",
            "bouncePointHasZeroVelocity",
            "bouncePointHasUnitScale",
            "phaseCurveConstraintOwned",
            "timeDerivativeIdentificationStillRequired",
        ],
        "DASHI/Quantum/QuantumBirthmarkKottlerHorizonBracketExact.agda": [
            "innerHorizonBracket",
            "outerHorizonBracket",
            "shellRadiusInsideStaticPatch",
            "globalGeodesicCompletenessStillNotProved",
        ],
    }
    for rel, tokens in expected.items():
        path = ROOT / rel
        assert path.exists(), rel
        text = path.read_text()
        for token in tokens:
            assert token in text, (rel, token)

    terminal = (ROOT / "DASHI/Quantum/QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact.agda").read_text()
    for token in [
        "staticTiltedWallNoGoOwned",
        "horizonThermalHubbleScalingOwned",
        "closedDeSitterBouncePhaseCurveOwned",
        "kottlerHorizonBracketingOwned",
    ]:
        assert token in terminal

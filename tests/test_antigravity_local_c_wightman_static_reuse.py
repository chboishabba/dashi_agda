from pathlib import Path

MODULE = Path("DASHI/Physics/Foundations/CMP119AntigravityLocalCWightmanTerminalToStaticExact.agda")


def test_wightman_terminal_reuses_one_selected_operator_for_static_promotion():
    text = MODULE.read_text()
    required = [
        "LocalCWightmanTerminalProducers",
        "compileLocalCWightmanTerminalToStaticReceipt",
        "compiledWightmanAmplitudeUsesAffineCalibration",
        "selectedOperatorContinuationPackageAlreadyShared = true",
        "independentPinnedBoostTraceSplitRequired = false",
        "independentStaticMetricResponseAfterWightmanTerminalRequired = false",
        "affineNormalizationAndCosmologicalConventionStillRequired = true",
    ]
    for needle in required:
        assert needle in text

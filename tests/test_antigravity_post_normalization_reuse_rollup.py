from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_reuse_rollup_imports_new_r136_tt_si_experiment_and_four_channel_frontiers():
    text = read("DASHI/Physics/ExoticGravity/AntigravityPostNormalizationReuseEverything.agda")
    for token in (
        "AntigravityPostNormalizationReuseMaxCutExact",
        "CMP119AntigravityPostScalarR136ReuseMaxCutExact",
        "CMP119AntigravityR136ToStaticVacuumPromotionExact",
        "CMP119AntigravityR136StaticPairToDifferentialExact",
        "CMP119AntigravityPinnedLocalCTerminalToStaticExact",
        "AntigravityDifferentialTTDonorMaxCutExact",
        "AntigravitySICalibrationDonorMaxCutExact",
        "AntigravityMatchedControlExperimentDonorMaxCutExact",
        "AntigravitySameStateFourChannelDiscriminatorExact",
        "AntigravityExperimentPortfolioExact",
    ):
        assert token in text


def test_static_response_reuse_does_not_recharge_r109_sign_tail():
    text = read("DASHI/Physics/ExoticGravity/AntigravityPostNormalizationReuseMaxCutExact.agda")
    for token in (
        "typedPinnedLocalCTerminalStillRequiredForStaticReuse",
        "r136FiniteAnchorTailRequiredForStaticResponseReuse",
        "r136StrictFinitePlusTailMarginRequiredForStaticResponseReuse",
        "r136FiniteAnchorTailStillRequiredForIndependentSignRoute",
        "r136StrictFinitePlusTailMarginStillRequiredForIndependentSignRoute",
    ):
        assert token in text
    assert "r136FiniteAnchorTailRequiredForStaticResponseReuse = false" in text
    assert "r136StrictFinitePlusTailMarginRequiredForStaticResponseReuse = false" in text

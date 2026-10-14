from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_reuse_rollup_imports_new_r136_tt_si_and_experiment_frontiers():
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
    ):
        assert token in text

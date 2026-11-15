from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_vacuum_collision_is_recast_as_experimental_coordinate_design():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumControlCoordinateDesignExact.agda"
    )
    for token in (
        "constantVacuumCoordinate",
        "constantVacuumSourceDimension",
        "constantVacuumCoordinateSeparatesCanonicalCollision",
        "projectedVacuumCoordinate",
        "projectedVacuumCoordinateSeparatesCanonicalCollision",
        "VacuumSelectiveControl",
        "selectiveControlPreservesCurrentSourceView",
        "selectiveControlChangesConstantVacuum",
        "selectiveControlChangesProjectedVacuum",
        "selectiveControlMakesVacuumCoordinateModifiable",
        "VacuumSourceDifferenceWitness",
        "selectiveControlProducesNonzeroSourcePair",
    ):
        assert token in text


def test_post_normalization_frontier_consumes_selective_control_target():
    text = read(
        "DASHI/Physics/ExoticGravity/"
        "AntigravityPostNormalizationMaxCutExact.agda"
    )
    assert "CMP119AntigravityVacuumControlCoordinateDesignExact" in text
    assert "vacuumSelectiveControlTargetCompiled" in text
    assert "physicalVacuumSelectiveControlStillRequired" in text

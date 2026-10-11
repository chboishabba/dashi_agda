from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_vacuum_sequence_is_not_determined_by_coupling_and_erb_source_view():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumSequenceNonidentifiabilityExact.agda"
    )
    for token in (
        "replaceVacuum",
        "zeroVacuumSource",
        "unitVacuumSource",
        "sameCouplingAfterVacuumReplacement",
        "sameESectorAfterVacuumReplacement",
        "sameRSectorAfterVacuumReplacement",
        "sameBSectorAfterVacuumReplacement",
        "zeroVacuumProjectsZero",
        "unitVacuumProjectsOne",
        "projectedVacuumSequencesDiffer",
        "couplingAndERBDoNotDetermineVacuum",
    ):
        assert token in text


def test_latest_single_vacuum_frontier_imports_nonidentifiability_owner():
    text = read(
        "DASHI/Physics/ExoticGravity/"
        "AntigravitySingleVacuumPhysicalPromotionMaxCutExact.agda"
    )
    assert "CMP119AntigravityVacuumSequenceNonidentifiabilityExact" in text
    assert "sourceVacuumSequenceRequiresIndependentPhysicalPayment" in text

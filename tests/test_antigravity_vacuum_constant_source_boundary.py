from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_balaban_source_boundary_supports_constant_normalization_role_only():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumConstantSourceBoundaryExact.agda"
    )
    for token in (
        "cmp109VacuumCountertermContainedInNormalizationFactors",
        "cmp119NamesVacuumEnergyCounterterm",
        "preferredScalarVacuumRepresentationSourceSupported",
        "sourceFixesVacuumNumericValue",
        "sourceIdentifiesVacuumConstantWithPhysicalLambda",
        "sourceProvesMetricResponseOfVacuumConstant",
    ):
        assert token in text

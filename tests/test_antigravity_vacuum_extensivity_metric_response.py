from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_vacuum_scalar_requires_extensive_volume_law_before_metric_response():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityVacuumExtensivityMetricResponseExact.agda"
    )
    for token in (
        "ExtensiveVacuumMetricFamily",
        "vacuumAction",
        "vacuumActionVariation",
        "vacuumActionVariationIsDensityTimesVolumeVariation",
        "metricIndependentConstantHasZeroVariation",
        "VacuumExtensivityToCosmologicalStressReceipt",
        "finiteScalarAloneDeterminesCosmologicalStress",
        "extensivityVolumeWeldStillRequired",
    ):
        assert token in text

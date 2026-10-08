from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_selected_source_vacuum_projector_reuses_literal_eq223_vacuum_term():
    text = read("DASHI/Physics/Foundations/CMP119AntigravitySelectedVacuumProjectorExact.agda")
    for token in (
        "selectedVacuumAmplitude",
        "plaquetteCoefficientProjector",
        "CMP119.vacuumEnergy source scale",
        "noIndependentVacuumReadoutRequired",
    ):
        assert token in text


def test_preferred_source_stress_route_reuses_selected_metric_family_closure():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityPreferredSourceGeometryBridgeExact.agda")
    for token in (
        "SelectedMetricFamilySU2ClosureInput",
        "selectedMetricFamilyDiagonalActiveSumNegative",
        "oldConstructorlessPinnedStressAuthorityRequired",
        "sourceVacuumAmplitude",
        "sourceScaledLambda",
    ):
        assert token in text


def test_terminal_marks_old_readout_and_ancestry_gates_obsolete_on_preferred_route():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    for token in (
        "stageAPreferredSourceGeometryBridge",
        "independentAbstractVacuumReadoutStillRequired",
        "oldConstructorlessPinnedStressAuthorityStillRequired",
        "preferredSelectedSourceStressSameObjectRouteAvailable",
    ):
        assert token in text

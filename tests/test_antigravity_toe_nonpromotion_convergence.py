from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/AntigravityTOENonPromotionBridgeExact.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED_PHYSICS = ROOT / "DASHI/Unified/Physics.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_bridge_reuses_exact_antigravity_owners():
    text = read(BRIDGE)
    for token in (
        "AntigravityMaterialBidiCrossPollinationExact",
        "AntigravityUnificationInteractionExact",
        "AntigravityResearchPromotionCutExact",
        "AntigravityStrongestConditionalTheoremExact",
        "CMP119AntigravityTraceVsActiveStressFirewallExact",
        "GRQFTMereologyBridgeExact",
    ):
        assert token in text


def test_bridge_exports_exact_nonpromotion_theorems():
    text = read(BRIDGE)
    for token in (
        "coarseAntigravityLabelIsNotPhysicalObservable",
        "negativeTraceAloneDoesNotCloseActiveStress",
        "traceAnomalyAloneDoesNotCloseRepulsion",
        "componentAgreementDoesNotCreateStressWeld",
        "currentRepoHasNoCanonicalPositiveComparativeAnomaly",
        "antigravityAnomalyDoesNotPromoteTerminalUnification",
        "strongConditionalTheoremDoesNotPromoteUniversalNegativeG",
        "strongConditionalTheoremDoesNotPromoteUniqueMechanism",
    ):
        assert token in text
    assert "postulate" not in text
    assert "{!!}" not in text
    assert "DASHI-Unification-Theorem" not in text


def test_bridge_is_attached_to_all_requested_toe_surfaces():
    import_line = "import DASHI.Unified.AntigravityTOENonPromotionBridgeExact"
    assert import_line in read(TOE)
    assert import_line in read(UNIFIER)
    assert import_line in read(UNIFIED_PHYSICS)


def test_toe_keeps_exact_gr_quantum_regression_authority():
    text = read(TOE)
    assert "import DASHI.Unified.GRQuantumProofTermRegression" in text
    assert "Do not replace this import with DASHI.Unifier placeholder axioms." in text

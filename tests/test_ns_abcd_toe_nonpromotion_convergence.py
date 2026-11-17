from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/NSABCDTOENonPromotionBridgeExact.agda"
VALIDATION = ROOT / "DASHI/Unified/NSABCDTOENonPromotionBridgeValidation.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
PHYSICS = ROOT / "DASHI/Unified/Physics.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_bridge_reuses_existing_ns_max_cut():
    text = read(BRIDGE)
    assert "NSABCDMaxCut20261002Exact" in text
    assert "record NSABCDTOEConvergenceReceipt" in text
    assert "canonicalNSABCDTOEConvergenceReceipt" in text


def test_bridge_exports_exact_nonpromotion_and_frontier_facts():
    text = read(BRIDGE)
    for token in (
        "aMaxCutHasThreeIrreducibleLeaves",
        "bDecisionHasTwoExternalLeaves",
        "bRealODEHasTwoInternalBridgeLeaves",
        "bPositiveFallbackHasSixLeaves",
        "r823NeedsNoAdditionalReserveEstimateAfterDecisionLeaves",
        "globalRationalHelicalProjectorLawsDoNotGateR829Decision",
        "cdIndependentReconstructionDoesNotGateSourceAudit",
        "nsClayPromotionRemainsFalse",
    ):
        assert token in text
    assert "postulate" not in text
    assert "{!!}" not in text
    assert "DASHI-Unification-Theorem" not in text


def test_exact_bridge_is_attached_to_requested_surfaces():
    import_line = "import DASHI.Unified.NSABCDTOENonPromotionBridgeExact"
    assert import_line in read(TOE)
    assert import_line in read(UNIFIER)
    assert import_line in read(PHYSICS)


def test_toe_reuses_exact_gr_quantum_regression():
    text = read(TOE)
    assert "import DASHI.Unified.GRQuantumProofTermRegression" in text
    assert "Do not replace this import with DASHI.Unifier placeholder axioms." in text


def test_unifier_does_not_use_placeholder_axioms_for_ns_bridge():
    text = read(UNIFIER)
    assert "nsABCDTOEConvergenceReceipt" in text
    assert "nsABCDClayPromotionRemainsFalse" in text
    assert "NSABCDTOE.canonicalNSABCDTOEConvergenceReceipt" in text
    assert "NSABCDTOE.nsClayPromotionRemainsFalse" in text


def test_validation_consumes_bridge_proofs():
    text = read(VALIDATION)
    for token in (
        "aFrontierRegression",
        "bDecisionRegression",
        "r823ReserveRegression",
        "helicalGateRegression",
        "clayNonPromotionRegression",
        "canonicalReceiptRegression",
    ):
        assert token in text

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeExact.agda"
REGRESSION = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeRegression.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"

def read(path: Path) -> str:
    assert path.is_file(), path
    return path.read_text(encoding="utf-8")

def test_exact_legal_owners_and_zkp_are_reused():
    text = read(BRIDGE)
    for token in (
        "CompositionalComplianceExact",
        "SensibLawOperationalSemanticBoundaryExact",
        "SensibLawLiveReviewMutationExact",
        "SensibLawMatterAcceptanceExact",
        "SensibLawLegalSourceAuthorityEvidenceExact",
        "SensibLawSemanticPromotionPolicy",
        "SensibLawDbNativeCorpusCompilerExact",
        "GovernedLegalWorkflowTOEInvariantHandoff",
        "canonicalGovernedLegalWorkflowTOEInvariantHandoff",
        "GovernedLegalWorkflowZKPReceipt",
        "canonicalGovernedLegalWorkflowZKPReceipt",
        "ITIL", "ISO 9000", "ISO/IEC 42001", "ISO/IEC 27001",
        "ISO/IEC 27701", "ISO/IEC 23894", "ISO 9241",
        "NIST AI RMF", "Six Sigma", "C4 and PlantUML", "ASD-STE100",
        "meta-introspector/zkperf", "meta-introspector/zos-server",
        "meta-introspector/erdfa-py", "meta-introspector/aristotle-cli-rs",
    ):
        assert token in text

def test_three_toe_consumers_reach_same_legal_handoff():
    toe, unifier, unified = map(read, (TOE, UNIFIER, UNIFIED))
    assert "toeGovernedLegalWorkflowInvariantHandoff" in toe
    assert "unifierGovernedLegalWorkflowInvariantHandoff" in unifier
    assert "governedLegalWorkflowTOEInvariantHandoff" in unified
    for token in ("TaskCompletionCreatesTruth", "SemanticPromotionTruthAuthorityClosed",
                  "CandidateSourceIsAuthoritative", "ExactReuseCreatesSemanticAuthority"):
        assert token in toe
        assert token in unifier

def test_regression_binds_unifier_to_canonical_bridge():
    text = read(REGRESSION)
    for token in (
        "unifierUsesCanonicalInvariantHandoff",
        "invariantHandoffUsesCanonicalGovernanceBoundary",
        "invariantHandoffUsesCanonicalPromotionBoundary",
        "invariantHandoffUsesCanonicalZKPReceipt",
        "zkpStandardsRemainDesignLenses",
        "zkpStandardsDoNotClaimCertification",
        "zkpESDSurfaceMutationRemainsForbidden",
        "unifierTaskCompletionAliasIsExact",
        "unifierSemanticPromotionTruthAuthorityAliasIsExact",
        "unifierExactReuseAuthorityAliasIsExact",
    ):
        assert token in text

def test_no_new_trust_escape():
    text = "\n".join(read(p) for p in (BRIDGE, REGRESSION, TOE, UNIFIER, UNIFIED))
    for token in ("postulate", "allow-unsolved-metas", "{-# TERMINATING #-}",
                  "{-# NO_POSITIVITY_CHECK #-}", "{!!}"):
        assert token not in text

def test_workflow_has_referee_preflight_and_esd_guard():
    text = read(WORKFLOW)
    for token in (
        "dashi-repo related",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
        "Reject ESD surface changes",
        "Reject trust escapes",
    ):
        assert token in text

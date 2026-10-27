from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

HANDOFF = ROOT / "DASHI/Unified/GovernedLegalWorkflowSourceGenealogyTOEExact.agda"
REGRESSION = ROOT / "DASHI/Unified/GovernedLegalWorkflowSourceGenealogyTOERegression.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_handoff_reuses_only_normalized_donors():
    text = read(HANDOFF)
    assert "GovernedLegalWorkflowTOEBridgeExact as Legal" in text
    assert "PNFSourceBoundaryTOEExact as Source" in text
    assert "IbrahimSnowball" not in text
    assert "Actionstep" not in text


def test_handoff_preserves_source_and_legal_nonpromotion():
    text = read(HANDOFF)
    for token in (
        "perceivedIndependenceFirewall",
        "repetitionIndependenceFirewall",
        "commonSourceEvidenceFirewall",
        "externalSourceTruthFirewall",
        "legalAuthorityTruthFirewall",
        "acceptedReviewApplicabilityFirewall",
        "semanticAdmissionLegalAuthorityFirewall",
        "canonicalGovernedLegalWorkflowSourceGenealogyHandoff",
    ):
        assert token in text


def test_handoff_reaches_all_required_toe_facades():
    root = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED)
    assert "GovernedLegalWorkflowSourceGenealogyTOEExact as LegalSourceGenealogy" in root
    assert "toeGovernedLegalWorkflowSourceGenealogyHandoff" in root
    assert "GovernedLegalWorkflowSourceGenealogyTOEExact as LegalSourceGenealogy" in unifier
    assert "unifierGovernedLegalWorkflowSourceGenealogyHandoff" in unifier
    assert "GovernedLegalWorkflowSourceGenealogyTOEExact as LegalSourceGenealogy" in unified
    assert "governedLegalWorkflowSourceGenealogyHandoff" in unified


def test_regression_binds_unifier_to_canonical_handoff():
    text = read(REGRESSION)
    for token in (
        "legalHandoffIsCanonical",
        "sourceBoundaryIsCanonical",
        "unifierHandoffIsCanonical",
        "unifierPerceivedIndependenceAliasIsExact",
        "unifierRepetitionAliasIsExact",
        "unifierCommonSourceAliasIsExact",
    ):
        assert token in text


def test_no_trust_escape_in_new_agda_lane():
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    )
    for path in (HANDOFF, REGRESSION):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} found in {path.relative_to(ROOT)}"


def test_workflow_executes_referee_preflight_and_kernel_for_handoff():
    text = read(WORKFLOW)
    for token in (
        "GovernedLegalWorkflowSourceGenealogyTOEExact.agda",
        "GovernedLegalWorkflowSourceGenealogyTOERegression.agda",
        "canonicalGovernedLegalWorkflowSourceGenealogyHandoff",
        "dashi-repo related",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
        "ESD surface change detected",
    ):
        assert token in text

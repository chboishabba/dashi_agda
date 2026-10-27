from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeExact.agda"
REGRESSION = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeRegression.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_bridge_reuses_existing_owners():
    text = read(BRIDGE)
    for token in (
        "CompositionalComplianceExact",
        "ITIRGovernanceControlCaseExact",
        "FormalisationGovernanceCapstoneExact",
        "SensibLawOperationalSemanticBoundaryExact",
        "SensibLawLiveReviewMutationExact",
        "SensibLawMatterAcceptanceExact",
        "SensibLawProvenanceSemanticStatusOrthogonalityExact",
        "SensibLawSourceRealisedLegalRuleExact",
        "SensibLawSourceConditionedApplicabilityViolationExact",
        "ITIRFederatedTypedWorldProjectionExact",
        "DistributedEpistemicFabricSourceAtlasExact",
        "AgentAuthorityTrajectoryExact",
    ):
        assert token in text


def test_bridge_exposes_normalized_zkp_receipt():
    text = read(BRIDGE)
    for token in (
        "GovernedLegalWorkflowZKPReceipt",
        "canonicalGovernedLegalWorkflowZKPReceipt",
        "objectiveRefs",
        "reuseRefs",
        "constructionRefs",
        "safetyInvariantRefs",
        "laneRefs",
        "preconditionRefs",
        "postconditionRefs",
        "governanceRefs",
        "verificationRefs",
    ):
        assert token in text


def test_standards_are_lenses_not_certification():
    text = read(BRIDGE)
    for token in (
        "ITIL",
        "ISO 9000",
        "ISO/IEC 42001",
        "ISO/IEC 27001",
        "ISO/IEC 27701",
        "ISO/IEC 23894",
        "ISO 9241",
        "NIST AI RMF",
        "Six Sigma",
        "C4 and PlantUML",
        "ASD-STE100",
    ):
        assert token in text
    assert "standardsCertificationClaimedIsFalse" in text


def test_meta_introspector_and_casey_attribution_is_preserved():
    text = read(BRIDGE)
    for token in (
        "toeMetaIntrospectorContribution",
        "toeMetaIntrospectorAttributionRule",
        "meta-introspector/zkperf",
        "meta-introspector/zos-server",
        "meta-introspector/erdfa-py",
        "meta-introspector/aristotle-cli-rs",
        "casey-git-clone",
    ):
        assert token in text
    assert "metaIntrospectorRepositoriesOwnDASHITheoremsIsFalse" in text


def test_authority_firewalls_are_exact_reuse():
    text = read(BRIDGE)
    for token in (
        "toeCaseySelectionDoesNotCreateWorldTruth",
        "toeFormalProofDoesNotCreateExternalWorldTruth",
        "toeKnowledgeDoesNotCreateExecutionAuthority",
    ):
        assert token in text


def test_bridge_is_attached_to_toe_root_and_unifier():
    toe = read(TOE)
    unifier = read(UNIFIER)
    assert "import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as LegalGovernance" in toe
    assert "toeGovernedLegalWorkflowZKPReceipt" in toe
    assert "toeCaseySelectionDoesNotCreateWorldTruth" in toe
    assert "toeKnowledgeDoesNotCreateExecutionAuthority" in toe
    assert "toeGovernedLegalWorkflowBoundary" in toe
    assert "toeWorkflowTaskCompletionDoesNotCreateTruth" in toe
    assert "toeDatabaseCommitDoesNotCreateSemanticAuthority" in toe
    assert "toeAcceptedReviewDoesNotPayApplicability" in toe
    assert "toeMatterAcceptanceDoesNotCreateTruth" in toe
    assert "toeCitationAloneDoesNotRealiseLegalRule" in toe
    assert "toeSemanticMeetDoesNotProveLegalApplicability" in toe
    assert "toeControlEvidenceDoesNotCreateTruth" in toe
    assert "toePassingControlDoesNotMeanCertified" in toe
    assert "import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as GovernanceTOE" in unifier
    assert "toeGovernedLegalWorkflowZKPReceipt" in unifier


def test_regression_binds_unifier_to_canonical_receipt():
    text = read(REGRESSION)
    assert "unifierUsesCanonicalZKPReceipt" in text
    assert "zkpStandardsRemainDesignLenses" in text
    assert "zkpStandardsDoNotClaimCertification" in text
    assert "zkpESDSurfaceMutationRemainsForbidden" in text


def test_new_governance_sources_have_no_trust_escape():
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    )
    for path in (BRIDGE, REGRESSION, TOE):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} found in {path.relative_to(ROOT)}"


def test_focused_workflow_contains_repo_intelligence_and_esd_guard():
    text = read(WORKFLOW)
    for token in (
        "dashi-repo related",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
        "ESD surface changed",
    ):
        assert token in text

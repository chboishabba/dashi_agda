from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeExact.agda"
REGRESSION = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeRegression.agda"
CANONICAL = ROOT / "DASHI/Unified/TOEGovernanceSemanticNonPromotionExact.agda"
VALIDATION = ROOT / "DASHI/Unified/TOEGovernanceSemanticNonPromotionValidation.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED_EVERYTHING = ROOT / "DASHI/Unified/DASHITOEEverything.agda"
TERMINAL = ROOT / "DASHI/Unified/DASHITOETerminalMaxCutExact.agda"


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


def test_focused_bridge_is_normalized_through_canonical_toe_owner():
    canonical = read(CANONICAL)
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified_everything = read(UNIFIED_EVERYTHING)
    terminal = read(TERMINAL)

    assert "import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as LegalWorkflow" in canonical
    for token in (
        "canonicalGovernedLegalWorkflowTOEBoundary",
        "canonicalGovernedLegalWorkflowZKPReceipt",
        "canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary",
        "canonicalExactNonFactorabilityResidualCompilerBoundary",
        "canonicalConsumerResearchAdmissibilityStopBoundary",
        "canonicalClosedIsNotAdequateBoundary",
        "canonicalMaboRevisionReopenBoundary",
        "canonicalRevisionReReviewPropagationBoundary",
        "canonicalLegalWorldRevisionReconstructionBoundary",
    ):
        assert token in canonical

    assert "import DASHI.Unified.TOEGovernanceSemanticNonPromotionExact as Governance" in toe
    assert "toeGovernanceHandoff" in toe
    assert "toeNoFreshDemandDoesNotProveConsumerAdequacy" in toe
    assert "toeExactNonfactorabilityMayReopenClosedFrontier" in toe
    assert "toeRevisionChangeReopensContextBeforeIdentity" in toe
    assert "toeLatestRevisionLookupDoesNotPayContextReview" in toe

    assert "import DASHI.Unified.TOEGovernanceSemanticNonPromotionExact as GovernanceTOE" in unifier
    assert "toeGovernanceHandoff" in unifier
    assert "toeWorkflowTaskCompletionDoesNotCreateTruth" in unifier
    assert "toeNoFreshDemandDoesNotProveConsumerAdequacy" in unifier
    assert "toeExactNonfactorabilityMayReopenClosedFrontier" in unifier

    assert "open import DASHI.Unified.TOEGovernanceSemanticNonPromotionExact public" in unified_everything
    assert "governanceHandoff : Governance.TOEGovernanceHandoff" in terminal
    assert "Governance.canonicalTOEGovernanceHandoff" in terminal


def test_regression_binds_unifier_to_canonical_receipt():
    text = read(REGRESSION)
    assert "unifierUsesCanonicalZKPReceipt" in text
    assert "zkpStandardsRemainDesignLenses" in text
    assert "zkpStandardsDoNotClaimCertification" in text
    assert "zkpESDSurfaceMutationRemainsForbidden" in text


def test_canonical_owner_keeps_esd_import_only_and_attribution():
    text = read(CANONICAL)
    assert "import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards" in text
    assert "standardMentionCannotCreateConformity" in text
    assert "citationCannotCreateProof" in text
    assert "citationCannotCreateAuthority" in text
    assert "attributionBoundary = Attribution.canonicalAttributionSnowballBoundary" in text


def test_new_governance_sources_have_no_trust_escape():
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    )
    for path in (BRIDGE, REGRESSION, CANONICAL, VALIDATION, TOE, UNIFIER):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} found in {path.relative_to(ROOT)}"


def test_canonical_validation_checks_exact_owner_types():
    text = read(VALIDATION)
    for token in (
        "Governance.toeRuntimeCoordinateCompletenessDoesNotProveFormalAdequacy",
        "Governance.toeTheoremBackedAdequacyRequiresAdequateFor",
        "Governance.toeApproximateCollisionCannotPromoteExactResidual",
        "Governance.toeFrontierClosureDoesNotProveConsumerAdequacy",
        "Governance.toeNoFreshDemandDoesNotProveConsumerAdequacy",
        "Governance.toeExactNonfactorabilityMayReopenClosedFrontier",
        "Governance.toeRevisionChangeReopensContextBeforeIdentity",
        "Governance.toeLatestRevisionLookupDoesNotPayContextReview",
        "Governance.toeRevisionReopenDoesNotCreateClaimTruth",
        "Governance.toeRevisionRereviewDoesNotChangeClaimTruth",
    ):
        assert token in text

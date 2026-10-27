from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeExact.agda"
REGRESSION = ROOT / "DASHI/Unified/GovernedLegalWorkflowTOEBridgeRegression.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED_EVERYTHING = ROOT / "DASHI/Unified/Everything.agda"
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
        "SLRReviewPromoteAbstainConsumerExact",
        "SLRRuntimeValidationHandoffExact",
        "SLRValidationRoadmapPromotionExact",
        "SensibLawLegalSemanticAdmissionFrontierExact",
        "SensibLawSemanticExpansionSoftwareValidationExact",
    ):
        assert token in text


def test_bridge_exposes_canonical_invariant_handoff():
    text = read(BRIDGE)
    for token in (
        "GovernedLegalWorkflowTOEInvariantHandoff",
        "canonicalGovernedLegalWorkflowTOEInvariantHandoff",
        "governanceBoundaryIsCanonical",
        "promotionBoundaryIsCanonical",
        "zkpReceiptIsCanonical",
        "taskCompletionNonPromotion",
        "runtimeParityTruthFirewall",
        "parserAdmissionFirewall",
        "caseySelectionTruthFirewall",
        "formalProofExternalTruthFirewall",
        "knowledgeExecutionAuthorityFirewall",
    ):
        assert token in text


def test_bridge_exposes_normalized_zkp_receipt():
    text = read(BRIDGE)
    for token in (
        "GovernedLegalWorkflowZKPReceipt",
        "canonicalGovernedLegalWorkflowZKPReceipt",
        "GovernedLegalWorkflowIntrospectiveZKPFrame",
        "canonicalGovernedLegalWorkflowIntrospectiveZKPFrame",
        "IntrospectiveProofLoopExact",
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
    assert "toeGovernedLegalWorkflowInvariantHandoff" in toe
    assert "toeGovernedLegalWorkflowZKPReceipt" in toe
    assert "toeGovernedLegalWorkflowIntrospectiveZKPFrame" in toe
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
    assert "toeGovernedLegalWorkflowPromotionBoundary" in toe
    assert "toeReviewEligibilityDoesNotCreatePromotion" in toe
    assert "toeRuntimeParityDoesNotCreateWorldTruth" in toe
    assert "toeDiagnosticStreamDoesNotCreateLegalCertification" in toe
    assert "toeProjectionDoesNotCreateClaimTruth" in toe
    assert "toeReviewRouterDoesNotCreateConsumerAdequacy" in toe
    assert "toeParserCandidateDoesNotAuthorizeAdmission" in toe
    assert "toeResidualPriorityDoesNotCreateTruthConfidence" in toe
    assert "toeAdmissionReceiptDoesNotPublishGeneration" in toe
    assert "toeSoftwareValidationDoesNotAuthorizePublication" in toe
    assert "toeLaterValidationDoesNotRewriteCertifiedBaseline" in toe
    assert "import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as GovernanceTOE" in unifier
    assert "toeGovernedLegalWorkflowInvariantHandoff" in unifier
    assert "toeGovernedLegalWorkflowZKPReceipt" in unifier
    assert "toeGovernedLegalWorkflowIntrospectiveZKPFrame" in unifier
    assert "toeGovernedLegalWorkflowPromotionBoundary" in unifier
    assert "toeReviewEligibilityDoesNotCreatePromotion" in unifier
    assert "toeRuntimeParityDoesNotCreateWorldTruth" in unifier
    assert "toeParserCandidateDoesNotAuthorizeAdmission" in unifier
    assert "toeSoftwareValidationDoesNotAuthorizePublication" in unifier


def test_bridge_is_attached_to_unified_everything():
    text = read(UNIFIED_EVERYTHING)
    assert "GovernedLegalWorkflowTOEBridgeExact as LegalGovernance" in text
    assert "governedLegalWorkflowTOEBoundary" in text
    assert "governedLegalWorkflowTOEInvariantHandoff" in text
    assert "governedLegalWorkflowIntrospectiveZKPFrame" in text


def test_governance_restack_preserves_current_toe_donors():
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED_EVERYTHING)
    for token in (
        "YMGoal1TOECompatibilityExact",
        "BalabanRGTOERegression",
    ):
        assert token in toe
        assert token in unifier
    assert "BalabanRGTOERegression" in unified


def test_regression_binds_unifier_to_canonical_receipt():
    text = read(REGRESSION)
    assert "unifierUsesCanonicalInvariantHandoff" in text
    assert "invariantHandoffUsesCanonicalGovernanceBoundary" in text
    assert "invariantHandoffUsesCanonicalPromotionBoundary" in text
    assert "invariantHandoffUsesCanonicalZKPReceipt" in text
    assert "unifierUsesCanonicalZKPReceipt" in text
    assert "unifierUsesCanonicalIntrospectiveZKPFrame" in text
    assert "invariantHandoffUsesCanonicalIntrospectiveZKPFrame" in text
    assert "zkpStandardsRemainDesignLenses" in text
    assert "zkpStandardsDoNotClaimCertification" in text
    assert "zkpESDSurfaceMutationRemainsForbidden" in text
    assert "unifierUsesCanonicalPromotionBoundary" in text
    assert "reviewEligibilityStillDoesNotCreatePromotion" in text
    assert "runtimeParityStillDoesNotCreateWorldTruth" in text
    assert "parserCandidateStillDoesNotAuthorizeAdmission" in text
    assert "softwareValidationStillDoesNotCreatePublication" in text


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
        "canonicalGovernedLegalWorkflowTOEInvariantHandoff",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
        "ESD surface changed",
    ):
        assert token in text


def test_semantic_authority_and_bound_acquisition_are_in_toe_graph():
    bridge = read(BRIDGE)
    toe = read(TOE)
    unifier = read(UNIFIER)
    regression = read(REGRESSION)

    for token in (
        "DASHI.Interop.SensibLawSemanticPromotionPolicy",
        "DASHI.Core.BoundAcquisitionDemandExact",
        "toeSemanticPromotionTruthAuthorityClosed",
        "toeSemanticPromotionLegalAuthorityClosed",
        "toeSemanticPromotionAllAuthorityClosed",
        "toeBoundAcquisitionDoesNotPayRequirement",
        "toeBoundAcquisitionDoesNotCloseConsumer",
        "toeProducerIdentityDoesNotIdentifyResidual",
    ):
        assert token in bridge

    for text in (toe, unifier):
        for token in (
            "toeSemanticPromotionTruthAuthorityClosed",
            "toeSemanticPromotionLegalAuthorityClosed",
            "toeSemanticPromotionAllAuthorityClosed",
            "toeBoundAcquisitionDoesNotPayRequirement",
            "toeBoundAcquisitionDoesNotCloseConsumer",
            "toeProducerIdentityDoesNotIdentifyResidual",
        ):
            assert token in text

    for token in (
        "unifierSemanticPromotionTruthAuthorityAliasIsExact",
        "unifierSemanticPromotionLegalAuthorityAliasIsExact",
        "unifierSemanticPromotionAllAuthorityAliasIsExact",
        "unifierBoundAcquisitionPaymentAliasIsExact",
        "unifierBoundAcquisitionClosureAliasIsExact",
        "unifierProducerIdentityResidualAliasIsExact",
    ):
        assert token in regression


def test_unified_facade_reexports_new_governance_firewalls():
    unified = read(UNIFIED_EVERYTHING)
    for token in (
        "governedSemanticPromotionTruthAuthorityClosed",
        "governedSemanticPromotionLegalAuthorityClosed",
        "governedSemanticPromotionAllAuthorityClosed",
        "governedBoundAcquisitionDoesNotPayRequirement",
        "governedBoundAcquisitionDoesNotCloseConsumer",
        "governedProducerIdentityDoesNotIdentifyResidual",
    ):
        assert token in unified


def test_legal_source_authority_handoff_is_exact():
    bridge = read(BRIDGE)
    regression = read(REGRESSION)
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED_EVERYTHING)

    assert "SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority" in bridge
    for token in (
        "toeCandidateSourceDoesNotCloseAuthority",
        "toeCurrentValidityDoesNotAutomaticallyEstablishApplicability",
        "toeSemanticAdmissionDoesNotBecomeLegalSourceAuthority",
    ):
        assert token in bridge

    for text, prefix in (
        (toe, "toe369"),
        (unifier, "unifier"),
        (unified, "unified"),
    ):
        for suffix in (
            "LegalCandidateIsNotAuthority",
            "LegalValidityIsNotApplicability",
            "SemanticAdmissionIsNotLegalAuthority",
        ):
            assert prefix + suffix in text

    for token in (
        "unifierLegalCandidateIsNotAuthority",
        "unifierLegalValidityIsNotApplicability",
        "unifierSemanticAdmissionIsNotLegalAuthority",
    ):
        assert token in regression


def test_exact_reuse_firewalls_reach_all_toe_facades():
    bridge = read(BRIDGE)
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED_EVERYTHING)
    regression = read(REGRESSION)

    for token in (
        "SensibLawDbNativeCorpusCompilerExact as DbNative",
        "toeExactReuseDoesNotCreateSemanticAdmission",
        "toeExactReuseDoesNotCreateSemanticAuthority",
        "toeExactReuseDoesNotCreateApplicability",
        "toeExactReuseDoesNotCreateEntityIdentity",
        "toeExactReuseDoesNotCreatePropositionIdentity",
        "toeExactReuseDoesNotCreateEventIdentity",
        "toeExactReuseDoesNotCreateClaimTruth",
        "exactReuseAdmissionFirewall",
        "exactReuseAuthorityFirewall",
        "exactReuseApplicabilityFirewall",
        "exactReuseClaimTruthFirewall",
    ):
        assert token in bridge

    for token in (
        "toeExactReuseDoesNotCreateSemanticAdmission",
        "toeExactReuseDoesNotCreateSemanticAuthority",
        "toeExactReuseDoesNotCreateApplicability",
        "toeExactReuseDoesNotCreateEntityIdentity",
        "toeExactReuseDoesNotCreatePropositionIdentity",
        "toeExactReuseDoesNotCreateEventIdentity",
        "toeExactReuseDoesNotCreateClaimTruth",
    ):
        assert token in toe
        assert token in unifier

    for token in (
        "governedExactReuseDoesNotCreateSemanticAdmission",
        "governedExactReuseDoesNotCreateSemanticAuthority",
        "governedExactReuseDoesNotCreateApplicability",
        "governedExactReuseDoesNotCreateEntityIdentity",
        "governedExactReuseDoesNotCreatePropositionIdentity",
        "governedExactReuseDoesNotCreateEventIdentity",
        "governedExactReuseDoesNotCreateClaimTruth",
    ):
        assert token in unified

    for token in (
        "unifierExactReuseAdmissionAliasIsExact",
        "unifierExactReuseAuthorityAliasIsExact",
        "unifierExactReuseApplicabilityAliasIsExact",
        "unifierExactReuseClaimTruthAliasIsExact",
        "invariantHandoffCarriesExactReuseAdmissionFirewall",
        "invariantHandoffCarriesExactReuseAuthorityFirewall",
        "invariantHandoffCarriesExactReuseApplicabilityFirewall",
        "invariantHandoffCarriesExactReuseClaimTruthFirewall",
    ):
        assert token in regression


def test_direct_legal_governance_firewalls_reach_all_three_toe_facades():
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED_EVERYTHING)
    bridge = read(BRIDGE)

    bridge_tokens = (
        "toeDurableReviewStateDoesNotCreateTruth",
        "toeAcceptanceReceiptDoesNotMutateMatter",
        "toeExternalSourceDoesNotAdmitTruth",
        "toeLegalAuthorityDoesNotCreateTruthStatus",
        "toePromotionStageDoesNotBypassPromotionAuthority",
        "toeSourceRealisedWrongTypeDoesNotAutoViolate",
        "toeElementsDoNotEraseExceptionsOrDefences",
        "toeKernelClosureDoesNotMeanSemanticClosure",
        "toeFormalProofDoesNotCreateExternalWorldTruth",
        "toeSameSystemDoesNotAutomaticallyCloseAuthority",
        "toeDocumentRoleDoesNotSupplyLegalSourceAuthority",
        "toeCanonicalLegalSourceAuthorityBoundary",
    )
    for token in bridge_tokens:
        assert token in bridge

    toe_tokens = (
        "toe369DurableReviewStateDoesNotCreateTruth",
        "toe369AcceptanceReceiptDoesNotMutateMatter",
        "toe369ExternalSourceDoesNotAdmitTruth",
        "toe369LegalAuthorityDoesNotCreateTruthStatus",
        "toe369PromotionStageDoesNotBypassPromotionAuthority",
        "toe369SourceRealisedWrongTypeDoesNotAutoViolate",
        "toe369ElementsDoNotEraseExceptionsOrDefences",
        "toe369KernelClosureDoesNotMeanSemanticClosure",
        "toe369FormalProofDoesNotCreateExternalWorldTruth",
        "toe369ComplianceCompositionRetainsIntermediateWitness",
        "toe369SameLegalSystemDoesNotCloseAuthority",
        "toe369DocumentRoleDoesNotSupplyLegalSourceAuthority",
        "toe369CanonicalLegalSourceAuthorityBoundary",
    )
    for token in toe_tokens:
        assert token in toe

    unifier_tokens = (
        "unifierDurableReviewStateDoesNotCreateTruth",
        "unifierAcceptanceReceiptDoesNotMutateMatter",
        "unifierExternalSourceDoesNotAdmitTruth",
        "unifierLegalAuthorityDoesNotCreateTruthStatus",
        "unifierPromotionStageDoesNotBypassPromotionAuthority",
        "unifierSourceRealisedWrongTypeDoesNotAutoViolate",
        "unifierElementsDoNotEraseExceptionsOrDefences",
        "unifierKernelClosureDoesNotMeanSemanticClosure",
        "unifierFormalProofDoesNotCreateExternalWorldTruth",
        "unifierComplianceCompositionRetainsIntermediateWitness",
        "unifierSameLegalSystemDoesNotCloseAuthority",
        "unifierDocumentRoleDoesNotSupplyLegalSourceAuthority",
        "unifierCanonicalLegalSourceAuthorityBoundary",
    )
    for token in unifier_tokens:
        assert token in unifier

    unified_tokens = (
        "governedDurableReviewStateDoesNotCreateTruth",
        "governedAcceptanceReceiptDoesNotMutateMatter",
        "governedExternalSourceDoesNotAdmitTruth",
        "governedLegalAuthorityDoesNotCreateTruthStatus",
        "governedPromotionStageDoesNotBypassPromotionAuthority",
        "governedSourceRealisedWrongTypeDoesNotAutoViolate",
        "governedElementsDoNotEraseExceptionsOrDefences",
        "governedKernelClosureDoesNotMeanSemanticClosure",
        "governedFormalProofDoesNotCreateExternalWorldTruth",
        "governedComplianceCompositionRetainsIntermediateWitness",
        "governedSameLegalSystemDoesNotCloseAuthority",
        "governedDocumentRoleDoesNotSupplyLegalSourceAuthority",
        "governedCanonicalLegalSourceAuthorityBoundary",
    )
    for token in unified_tokens:
        assert token in unified


def test_direct_legal_governance_regression_binds_unifier_to_bridge():
    text = read(REGRESSION)
    for token in (
        "unifierDurableReviewTruthAliasIsExact",
        "unifierAcceptanceMutationAliasIsExact",
        "unifierExternalSourceTruthAliasIsExact",
        "unifierLegalAuthorityTruthAliasIsExact",
        "unifierPromotionAuthorityAliasIsExact",
        "unifierWrongTypeViolationAliasIsExact",
        "unifierExceptionsDefencesAliasIsExact",
        "unifierComplianceWitnessAliasIsCanonical",
        "unifierCanonicalLegalAuthorityBoundaryIsExact",
    ):
        assert token in text



def test_native_follow_provider_and_expert_firewalls_reach_all_toe_facades():
    bridge = read(BRIDGE)
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED_EVERYTHING)
    regression = read(REGRESSION)

    for token in (
        "toeNativeLegalFollowDoesNotCreateLegalAuthority",
        "toeProviderFailureDoesNotMakePropositionFalse",
        "toeExpertProductionPromotesAnyAuthorityIsFalse",
        "nativeLegalFollowAuthorityFirewall",
        "providerFailureNegativeEvidenceFirewall",
        "expertProductionAuthorityClosed",
    ):
        assert token in bridge

    for token in (
        "toe369NativeLegalFollowDoesNotCreateLegalAuthority",
        "toe369ProviderFailureDoesNotMakePropositionFalse",
        "toe369ExpertProductionPromotesAnyAuthorityIsFalse",
    ):
        assert token in toe

    for token in (
        "unifierNativeLegalFollowDoesNotCreateLegalAuthority",
        "unifierProviderFailureDoesNotMakePropositionFalse",
        "unifierExpertProductionPromotesAnyAuthorityIsFalse",
    ):
        assert token in unifier

    for token in (
        "governedNativeLegalFollowDoesNotCreateLegalAuthority",
        "governedProviderFailureDoesNotMakePropositionFalse",
        "governedExpertProductionPromotesAnyAuthorityIsFalse",
    ):
        assert token in unified

    for token in (
        "unifierNativeLegalFollowAuthorityAliasIsExact",
        "unifierProviderFailureEvidenceAliasIsExact",
        "unifierExpertProductionAuthorityAliasIsExact",
        "invariantHandoffCarriesNativeLegalFollowAuthorityFirewall",
        "invariantHandoffCarriesProviderFailureEvidenceFirewall",
        "invariantHandoffCarriesExpertProductionAuthorityClosure",
    ):
        assert token in regression

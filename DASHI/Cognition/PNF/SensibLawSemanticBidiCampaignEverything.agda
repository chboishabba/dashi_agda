import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact as Attribution
import DASHI.Cognition.PNF.SensibLawAntecedentIdentityRefinementBidiExact as Identity
import DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact as Scope
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact as LegalRole
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as LegalChain
import DASHI.Cognition.PNF.SensibLawDocumentWorldSemanticStatusBidiExact as Context
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawConsumerQueryLeastPrivilegeRegressionExact as LeastPrivilege
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact as Routing
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as EvidenceBridge
import DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact as LegalEvidence
import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as LegalJurisdiction
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority
import DASHI.Cognition.PNF.SensibLawResolvedScopePlannerLiveExact as ResolvedScopeLive
import DASHI.Cognition.PNF.SensibLawPdfActiveRequirementPlannerLiveExact as PdfPlanner
import DASHI.Cognition.PNF.SensibLawSemanticLiveVerticalEverything as Live
import DASHI.Cognition.PNF.SensibLawUnifiedPNFIntakeReentrySpineExact as IntakeReentry
import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as PersistentTrace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as ChronologyContestation
import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact as ReviewWorkstation
import DASHI.Cognition.PNF.SensibLawCandidateEventDiscoveryExact as EventDiscovery
import DASHI.Cognition.PNF.SensibLawOperationalSemanticBoundaryExact as OperationalBoundary
import DASHI.Cognition.PNF.SensibLawLiveReviewMutationExact as LiveReviewMutation
import DASHI.Cognition.PNF.SensibLawConversationalSourceFamilyExact as ConversationalSource
import DASHI.Cognition.PNF.SensibLawMatterContextProjectionExact as MatterContext
import DASHI.Cognition.PNF.SensibLawMatterWorkspaceProjectionExact as MatterWorkspace
import DASHI.Cognition.PNF.SensibLawMinimalMatterHandoffExact as MinimalHandoff
import DASHI.Cognition.PNF.SensibLawMatterAcceptanceExact as MatterAcceptance
import DASHI.Cognition.PNF.SensibLawWorkProductCoverageExact as WorkProductCoverage
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationExact as GenericIngest
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact as GenericIngestWeld
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldRegression as GenericIngestWeldRegression
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceExact as LongDocumentPersistence
import DASHI.Cognition.PNF.SensibLawLongDocumentPersistenceRegression as LongDocumentPersistenceRegression
import DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerExact as DbNativeCorpus
import DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerRegression as DbNativeCorpusRegression

module DASHI.Cognition.PNF.SensibLawSemanticBidiCampaignEverything where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)


data BidiCampaign : Set where
  attributionPropositionCampaign : BidiCampaign
  occurrenceCampaign : BidiCampaign
  antecedentIdentityCampaign : BidiCampaign
  scopeCompositionCampaign participantLegalRoleCampaign legalApplicabilityCampaign : BidiCampaign
  documentWorldContextCampaign consumerQueryDemandCampaign : BidiCampaign
  activeRequirementPlannerCampaign requirementProducerRoutingCampaign : BidiCampaign
  liveProducerEvidenceCampaign resolvedLegalEvidenceCampaign : BidiCampaign
  resolvedLegalJurisdictionCampaign legalSourceAuthorityCampaign : BidiCampaign
  resolvedScopePlannerCampaign pdfPlannerRegressionCampaign : BidiCampaign

data CampaignReadiness : Set where
  typeOwnerPresent : CampaignReadiness
  runtimeProducerNeeded : CampaignReadiness
  consumerMaySkip : CampaignReadiness

campaignReadiness : BidiCampaign → CampaignReadiness
campaignReadiness attributionPropositionCampaign = typeOwnerPresent
campaignReadiness occurrenceCampaign = typeOwnerPresent
campaignReadiness antecedentIdentityCampaign = typeOwnerPresent
campaignReadiness scopeCompositionCampaign = typeOwnerPresent
campaignReadiness participantLegalRoleCampaign = typeOwnerPresent
campaignReadiness legalApplicabilityCampaign = typeOwnerPresent
campaignReadiness documentWorldContextCampaign = typeOwnerPresent
campaignReadiness consumerQueryDemandCampaign = typeOwnerPresent
campaignReadiness activeRequirementPlannerCampaign = typeOwnerPresent
campaignReadiness requirementProducerRoutingCampaign = typeOwnerPresent
campaignReadiness liveProducerEvidenceCampaign = typeOwnerPresent
campaignReadiness resolvedLegalEvidenceCampaign = typeOwnerPresent
campaignReadiness resolvedLegalJurisdictionCampaign = typeOwnerPresent
campaignReadiness legalSourceAuthorityCampaign = typeOwnerPresent
campaignReadiness resolvedScopePlannerCampaign = typeOwnerPresent
campaignReadiness pdfPlannerRegressionCampaign = typeOwnerPresent

allCampaignTypeOwnersPresent : campaignReadiness attributionPropositionCampaign ≡ typeOwnerPresent
allCampaignTypeOwnersPresent = refl
executionPlannerOwnerPresent : campaignReadiness activeRequirementPlannerCampaign ≡ typeOwnerPresent
executionPlannerOwnerPresent = refl
producerRoutingOwnerPresent : campaignReadiness requirementProducerRoutingCampaign ≡ typeOwnerPresent
producerRoutingOwnerPresent = refl
liveProducerEvidenceOwnerPresent : campaignReadiness liveProducerEvidenceCampaign ≡ typeOwnerPresent
liveProducerEvidenceOwnerPresent = refl
resolvedLegalEvidenceOwnerPresent : campaignReadiness resolvedLegalEvidenceCampaign ≡ typeOwnerPresent
resolvedLegalEvidenceOwnerPresent = refl
resolvedLegalJurisdictionOwnerPresent : campaignReadiness resolvedLegalJurisdictionCampaign ≡ typeOwnerPresent
resolvedLegalJurisdictionOwnerPresent = refl
legalSourceAuthorityOwnerPresent : campaignReadiness legalSourceAuthorityCampaign ≡ typeOwnerPresent
legalSourceAuthorityOwnerPresent = refl
resolvedScopePlannerOwnerPresent : campaignReadiness resolvedScopePlannerCampaign ≡ typeOwnerPresent
resolvedScopePlannerOwnerPresent = refl
pdfPlannerRegressionOwnerPresent : campaignReadiness pdfPlannerRegressionCampaign ≡ typeOwnerPresent
pdfPlannerRegressionOwnerPresent = refl

claimDiscourseHasLiveInhabitant : Live.liveCampaignState Live.claimDiscourseLive ≡ Live.inhabitedRegression
claimDiscourseHasLiveInhabitant = refl
occurrenceHasLiveInhabitant : Live.liveCampaignState Live.occurrenceLive ≡ Live.inhabitedRegression
occurrenceHasLiveInhabitant = refl
identityRefinementHasLiveInhabitant : Live.liveCampaignState Live.identityRefinementLive ≡ Live.inhabitedRegression
identityRefinementHasLiveInhabitant = refl
scopeCompositionHasLiveInhabitant : Live.liveCampaignState Live.scopeCompositionLive ≡ Live.inhabitedRegression
scopeCompositionHasLiveInhabitant = refl
documentContextHasLiveInhabitant : Live.liveCampaignState Live.documentContextLive ≡ Live.inhabitedRegression
documentContextHasLiveInhabitant = refl
participantLegalRoleHasLiveInhabitant : Live.liveCampaignState Live.participantLegalRoleLive ≡ Live.inhabitedRegression
participantLegalRoleHasLiveInhabitant = refl
narrativeLegalGateHasLiveInhabitant : Live.liveCampaignState Live.narrativeLegalGateLive ≡ Live.inhabitedRegression
narrativeLegalGateHasLiveInhabitant = refl
resolvedScopePlannerHasLiveInhabitant : Planner.action ResolvedScopeLive.resolvedScopePlan ≡ Planner.reuseExisting
resolvedScopePlannerHasLiveInhabitant = ResolvedScopeLive.resolvedScopeReusesExisting

legalConsumerDoesNotImplyFullApplicabilityStack : Demand.LegalConsumerAlwaysNeedsApplicability → ⊥
legalConsumerDoesNotImplyFullApplicabilityStack = Demand.legalConsumerDoesNotAlwaysNeedApplicability
legalWhoSaidWhatHasNoApplicabilityObligation : Demand.Requires Consumer.legalConsumer Demand.whoSaidWhatQuery Demand.applicabilityCoordinate → ⊥
legalWhoSaidWhatHasNoApplicabilityObligation = LeastPrivilege.legalWhoSaidWhatDoesNotRequireApplicability
legalApplicabilityRequiresResolvedEvidence : Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.resolvedLegalEvidenceCoordinate
legalApplicabilityRequiresResolvedEvidence = LeastPrivilege.legalApplicabilityReallyRequiresResolvedEvidence
legalApplicabilityCannotBorrowEvidenceCandidate : Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.evidenceCandidateCoordinate → ⊥
legalApplicabilityCannotBorrowEvidenceCandidate = LeastPrivilege.legalApplicabilityDoesNotAcceptEvidenceCandidateInstead
legalApplicabilityRequiresLegalSourceAuthority : Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.legalSourceAuthorityCoordinate
legalApplicabilityRequiresLegalSourceAuthority = LeastPrivilege.legalApplicabilityReallyRequiresLegalSourceAuthority
legalApplicabilityDoesNotBorrowSemanticAdmissionAuthority : Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.semanticAdmissionAuthorityCoordinate → ⊥
legalApplicabilityDoesNotBorrowSemanticAdmissionAuthority = LeastPrivilege.legalApplicabilityDoesNotRequireSemanticAdmissionAuthority
legalApplicabilityRequiresResolvedJurisdiction : Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.resolvedLegalJurisdictionCoordinate
legalApplicabilityRequiresResolvedJurisdiction = LeastPrivilege.legalApplicabilityReallyRequiresResolvedJurisdiction
legalApplicabilityRequiresResolvedScope : Demand.Requires Consumer.legalConsumer Demand.legalApplicabilityQuery Demand.resolvedScopeCoordinate
legalApplicabilityRequiresResolvedScope = LeastPrivilege.legalApplicabilityReallyRequiresResolvedScope
unrequestedCoordinatesDoNotBlockConsumer : Demand.UnrequestedCoordinateMustResolve → ⊥
unrequestedCoordinatesDoNotBlockConsumer = Demand.unrequestedCoordinateDoesNotCountAsFailure
authorityUpdateDoesNotReparseSyntax : Demand.AuthorityChangeReparsesSyntax → ⊥
authorityUpdateDoesNotReparseSyntax = Demand.authorityChangeDoesNotReparseSyntax
broaderDemandPreservesSemanticCarrier : Demand.BroaderDemandRewritesSemanticCarrier → ⊥
broaderDemandPreservesSemanticCarrier = Demand.broaderDemandDoesNotRewriteCarrier
semanticAdmissionAuthorityCannotPayLegalSourceAuthority : Demand.SemanticAdmissionAuthorityPaysLegalSourceAuthority → ⊥
semanticAdmissionAuthorityCannotPayLegalSourceAuthority = Demand.semanticAdmissionAuthorityDoesNotPayLegalSourceAuthority

evidenceCandidateAndResolvedLegalEvidenceAreDistinct : Cross.EvidenceCandidateIsResolvedLegalEvidence → ⊥
evidenceCandidateAndResolvedLegalEvidenceAreDistinct = Cross.evidenceCandidateDoesNotEqualResolvedLegalEvidence
scopeCandidateAndResolvedScopeAreDistinct : Cross.ParserScopeCandidateIsResolvedScope → ⊥
scopeCandidateAndResolvedScopeAreDistinct = Cross.parserScopeCandidateDoesNotEqualResolvedScope
jurisdictionCandidateAndResolvedJurisdictionAreDistinct : Cross.JurisdictionCandidateIsResolvedLegalJurisdiction → ⊥
jurisdictionCandidateAndResolvedJurisdictionAreDistinct = Cross.jurisdictionCandidateDoesNotEqualResolvedLegalJurisdiction
parserEvidenceCannotPayResolvedLegalEvidence : LegalEvidence.ParserEvidencePaysResolvedLegalEvidence → ⊥
parserEvidenceCannotPayResolvedLegalEvidence = LegalEvidence.parserEvidenceDoesNotPayResolvedLegalEvidence
geographicMentionCannotPayResolvedLegalJurisdiction : LegalJurisdiction.GeographicMentionIsResolvedLegalJurisdiction → ⊥
geographicMentionCannotPayResolvedLegalJurisdiction = LegalJurisdiction.geographicMentionDoesNotResolveLegalJurisdiction
semanticAdmissionCannotBecomeLegalSourceAuthority : LegalAuthority.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
semanticAdmissionCannotBecomeLegalSourceAuthority = LegalAuthority.semanticAdmissionDoesNotBecomeLegalSourceAuthority

resolvedRequirementReusesExistingEvidence :
  ∀ {state active refs producer} →
  Planner.action (Planner.planRequirement
    (Planner.coordinateEvidenceReceipt {state} {active} Planner.currentResolved refs producer true refl true refl)
    "campaign:resolved") ≡ Planner.reuseExisting
resolvedRequirementReusesExistingEvidence = refl
unassessedRequirementInspectsEvidence :
  ∀ {state active refs producer} →
  Planner.action (Planner.planRequirement
    (Planner.coordinateEvidenceReceipt {state} {active} Planner.currentUnassessed refs producer true refl true refl)
    "campaign:unassessed") ≡ Planner.inspectForEvidence
unassessedRequirementInspectsEvidence = refl
missingRequirementAcquiresEvidence :
  ∀ {state active refs producer} →
  Planner.action (Planner.planRequirement
    (Planner.coordinateEvidenceReceipt {state} {active} Planner.currentMissing refs producer true refl true refl)
    "campaign:missing") ≡ Planner.acquireMissingEvidence
missingRequirementAcquiresEvidence = refl
staleRequirementRevalidatesWithoutReparse : Planner.StaleRequirementForcesFullReparse → ⊥
staleRequirementRevalidatesWithoutReparse = Planner.staleRequirementDoesNotForceFullReparse
semanticStateIsNotTotalEvidenceOracle : Planner.SemanticStateAloneTotalizesCoordinateEvidence → ⊥
semanticStateIsNotTotalEvidenceOracle = Planner.semanticStateAloneDoesNotTotalizeEvidence

documentContextHasDedicatedProducer : Routing.ProducerCanPopulate Cross.documentContextProducer Demand.documentContextCoordinate
documentContextHasDedicatedProducer = Routing.documentContextPopulatesContext
resolvedLegalEvidenceHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalEvidenceResolutionProducer Demand.resolvedLegalEvidenceCoordinate
resolvedLegalEvidenceHasDedicatedProducer = Routing.legalEvidencePopulatesResolvedEvidence
resolvedScopeHasDedicatedProducer : Routing.ProducerCanPopulate Cross.scopeResolutionProducer Demand.resolvedScopeCoordinate
resolvedScopeHasDedicatedProducer = Routing.scopeResolutionPopulatesResolvedScope
resolvedJurisdictionHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalJurisdictionProducer Demand.resolvedLegalJurisdictionCoordinate
resolvedJurisdictionHasDedicatedProducer = Routing.legalJurisdictionPopulatesResolvedJurisdiction
legalSourceAuthorityHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalSourceAuthorityProducer Demand.legalSourceAuthorityCoordinate
legalSourceAuthorityHasDedicatedProducer = Routing.legalSourcePopulatesAuthority
semanticAdmissionHasSeparateProducer : Routing.ProducerCanPopulate Cross.governedAdmissionProducer Demand.semanticAdmissionAuthorityCoordinate
semanticAdmissionHasSeparateProducer = Routing.governedAdmissionPopulatesSemanticAuthority
parserCannotPopulateLegalApplicability : Routing.ParserCanPopulateLegalApplicability → ⊥
parserCannotPopulateLegalApplicability = Routing.parserDoesNotOwnLegalApplicability
evidenceCandidateCannotPopulateResolvedLegalEvidence : Routing.EvidenceCandidateCanPopulateResolvedLegalEvidence → ⊥
evidenceCandidateCannotPopulateResolvedLegalEvidence = Routing.evidenceCandidateDoesNotOwnResolvedLegalEvidence
reuseNeedsNoProducerInvocation : Routing.invocationNeed Planner.reuseExisting ≡ Routing.noProducerInvocation
reuseNeedsNoProducerInvocation = refl

positiveProducerReceiptRequiresExactStateObject : EvidenceBridge.ReceiptAboutOtherPropositionPaysRequirement → ⊥
positiveProducerReceiptRequiresExactStateObject = EvidenceBridge.otherPropositionReceiptDoesNotPay
missingClassificationNeedsSearchReceipt : EvidenceBridge.MissingEvidenceMayBeInferredFromNoLocalConstructor → ⊥
missingClassificationNeedsSearchReceipt = EvidenceBridge.absenceOfConstructorDoesNotProveMissing

pdfPlannerReusesAttribution : Planner.action PdfPlanner.attributionPlan ≡ Planner.reuseExisting
pdfPlannerReusesAttribution = PdfPlanner.attributionReusesExisting
pdfPlannerReusesProposition : Planner.action PdfPlanner.propositionPlan ≡ Planner.reuseExisting
pdfPlannerReusesProposition = PdfPlanner.propositionReusesExisting
pdfPlannerReusesOccurrence : Planner.action PdfPlanner.occurrencePlan ≡ Planner.reuseExisting
pdfPlannerReusesOccurrence = PdfPlanner.occurrenceReusesExisting
pdfPlannerReusesDocumentContext : Planner.action PdfPlanner.documentContextPlan ≡ Planner.reuseExisting
pdfPlannerReusesDocumentContext = PdfPlanner.documentContextReusesExisting
pdfPlannerInspectsResolvedEvidence : Planner.action PdfPlanner.resolvedEvidencePlan ≡ Planner.inspectForEvidence
pdfPlannerInspectsResolvedEvidence = PdfPlanner.resolvedEvidenceNeedsInspection
pdfPlannerInspectsLegalSourceAuthority : Planner.action PdfPlanner.legalSourceAuthorityPlan ≡ Planner.inspectForEvidence
pdfPlannerInspectsLegalSourceAuthority = PdfPlanner.legalSourceAuthorityNeedsInspection
pdfPlannerInspectsResolvedScope : Planner.action PdfPlanner.resolvedScopePlan ≡ Planner.inspectForEvidence
pdfPlannerInspectsResolvedScope = PdfPlanner.resolvedScopeNeedsInspection
pdfPlannerInspectsResolvedJurisdiction : Planner.action PdfPlanner.resolvedJurisdictionPlan ≡ Planner.inspectForEvidence
pdfPlannerInspectsResolvedJurisdiction = PdfPlanner.resolvedJurisdictionNeedsInspection
pdfPaidPrefixDoesNotCloseApplicability : PdfPlanner.PaidPrefixMeansApplicabilityFullyResolved → ⊥
pdfPaidPrefixDoesNotCloseApplicability = PdfPlanner.paidPrefixDoesNotMeanFullApplicability

regexStillForbidden : Constitution.CompositionOnlyBoundary.regexMayProduceSemanticEvidence Constitution.canonicalCompositionOnlyBoundary ≡ false
regexStillForbidden = refl
candidateStillNeedsContext : Constitution.CompositionOnlyBoundary.semanticResolutionRequiresContextReceipt Constitution.canonicalCompositionOnlyBoundary ≡ true
candidateStillNeedsContext = refl
assertionStillNotTruth : Status.AssertionDeterminesTruth → ⊥
assertionStillNotTruth = Status.assertionDoesNotDetermineTruth
mentionStillNotOccurrence : Status.MentionDeterminesOccurrence → ⊥
mentionStillNotOccurrence = Status.mentionDoesNotDetermineOccurrence
agentStillNotDutyBearer : Status.LinguisticAgentDeterminesDutyBearer → ⊥
agentStillNotDutyBearer = Status.linguisticAgentDoesNotDetermineDutyBearer
applicabilityStillNotViolation : Status.ApplicabilityDeterminesViolation → ⊥
applicabilityStillNotViolation = Status.applicabilityDoesNotDetermineViolation
violationStillNotLiability : Status.ViolationDeterminesLiability → ⊥
violationStillNotLiability = Status.violationDoesNotDetermineLiability
consumerEquivalenceStillNotWorldIdentity : Context.ConsumerEquivalentMeansSameSemanticWorld → ⊥
consumerEquivalenceStillNotWorldIdentity = Context.consumerEquivalenceDoesNotIdentifyWorld
claimAssertionBoundary : Attribution.ClaimAssertionIsTruthProof → ⊥
claimAssertionBoundary = Attribution.claimAssertionDoesNotProveTruth
antecedentIdentityBoundary : Identity.UniqueAntecedentAutomaticallyClosesIdentity → ⊥
antecedentIdentityBoundary = Identity.uniqueAntecedentDoesNotAutoCloseIdentity
scopeTruthBoundary : Scope.ScopeResolutionProvesTruth → ⊥
scopeTruthBoundary = Scope.scopeResolutionDoesNotProveTruth
legalRoleBoundary : LegalRole.AgentAutomaticallyDutyBearer → ⊥
legalRoleBoundary = LegalRole.agentDoesNotAutoBecomeDutyBearer
legalChainBoundary : LegalChain.ApplicableAutomaticallyViolated → ⊥
legalChainBoundary = LegalChain.applicabilityDoesNotAutoViolate

data TypeOwnerPresenceMeansCorpusResolved : Set where
data AggregateImportMeansKernelValidated : Set where
typeOwnersDoNotResolveCorpus : TypeOwnerPresenceMeansCorpusResolved → ⊥
typeOwnersDoNotResolveCorpus ()
aggregateImportDoesNotClaimKernelValidation : AggregateImportMeansKernelValidated → ⊥
aggregateImportDoesNotClaimKernelValidation ()

------------------------------------------------------------------------
-- M14.A Work Product Coverage remains a Matter projection.
------------------------------------------------------------------------

workProductCoveragePreservesMatter :
  WorkProductCoverage.CoverageJudgmentMutatesMatter → ⊥
workProductCoveragePreservesMatter =
  WorkProductCoverage.coverageJudgmentDoesNotMutateMatter

workProductCoverageDoesNotCreateTruth :
  WorkProductCoverage.WorkProductWordingIsSemanticAuthority → ⊥
workProductCoverageDoesNotCreateTruth =
  WorkProductCoverage.workProductWordingDoesNotCreateSemanticAuthority

unsupportedWorkProductCoverageDoesNotMeanFalse :
  WorkProductCoverage.UnsupportedCoverageMeansFalse → ⊥
unsupportedWorkProductCoverageDoesNotMeanFalse =
  WorkProductCoverage.unsupportedCoverageDoesNotMeanFalse

possiblyOmittedDoesNotBecomeDraftingDuty :
  WorkProductCoverage.PossiblyOmittedMeansShouldInclude → ⊥
possiblyOmittedDoesNotBecomeDraftingDuty =
  WorkProductCoverage.possiblyOmittedDoesNotMeanShouldInclude

forwardCoverageRemainsDistinctFromOmission :
  WorkProductCoverage.ForwardCoverageIsReverseOmission → ⊥
forwardCoverageRemainsDistinctFromOmission =
  WorkProductCoverage.forwardCoverageIsNotReverseOmission

------------------------------------------------------------------------
-- INGEST-1 generic source compilation remains below semantic admission.
------------------------------------------------------------------------

genericIngestKeepsProducerCaptureDistinct :
  GenericIngest.ProducerCaptureIsSourceIdentity → ⊥
genericIngestKeepsProducerCaptureDistinct =
  GenericIngest.producerCaptureDoesNotDetermineSourceIdentity

genericIngestKeepsSourceIdentityDistinctFromSemantics :
  GenericIngest.SourceIdentityIsSemanticInterpretation → ⊥
genericIngestKeepsSourceIdentityDistinctFromSemantics =
  GenericIngest.sourceIdentityDoesNotDetermineSemanticInterpretation

genericIngestKeepsOperationalObservationDistinct :
  GenericIngest.SemanticInterpretationIsOperationalObservation → ⊥
genericIngestKeepsOperationalObservationDistinct =
  GenericIngest.semanticInterpretationIsNotOperationalObservation

quotedMailDoesNotMultiplyWitnesses :
  GenericIngest.QuoteCreatesIndependentWitness → ⊥
quotedMailDoesNotMultiplyWitnesses =
  GenericIngest.quotedMailDoesNotCreateIndependentWitness

parseFailureDoesNotEraseSource :
  GenericIngest.ParseFailureDeletesSource → ⊥
parseFailureDoesNotEraseSource =
  GenericIngest.parseFailureDoesNotDeleteSource

ingestCandidateDoesNotBecomeTruth :
  GenericIngest.CandidateInterpretationDeterminesTruth → ⊥
ingestCandidateDoesNotBecomeTruth =
  GenericIngest.candidateInterpretationDoesNotDetermineTruth

------------------------------------------------------------------------
-- INGEST-1 canonical weld and lossless partition.
------------------------------------------------------------------------

genericIngestUsesCanonicalEvidenceCarrier :
  GenericIngestWeld.ProviderAdapterCreatesAlternateCanonicalCarrier → ⊥
genericIngestUsesCanonicalEvidenceCarrier =
  GenericIngestWeld.providerAdapterDoesNotCreateAlternateCanonicalCarrier

genericIngestDoesNotCreateProviderReviewShortcut :
  GenericIngestWeld.ProviderAdapterCreatesReviewShortcut → ⊥
genericIngestDoesNotCreateProviderReviewShortcut =
  GenericIngestWeld.providerAdapterDoesNotCreateReviewShortcut

genericIngestDoesNotCreateProviderProjectionShortcut :
  GenericIngestWeld.ProviderAdapterCreatesProjectionShortcut → ⊥
genericIngestDoesNotCreateProviderProjectionShortcut =
  GenericIngestWeld.providerAdapterDoesNotCreateProjectionShortcut

genericDocumentStructureDoesNotBecomeObservation :
  GenericIngestWeld.DocumentStructureCreatesSemanticObservation → ⊥
genericDocumentStructureDoesNotBecomeObservation =
  GenericIngestWeld.documentStructureDoesNotCreateSemanticObservation

genericParserSuccessDoesNotPayReview :
  GenericIngestWeld.ParserSuccessCreatesReviewPayment → ⊥
genericParserSuccessDoesNotPayReview =
  GenericIngestWeld.parserSuccessDoesNotCreateReviewPayment

genericParserResidualDoesNotCreateSourceAbsence :
  GenericIngestWeld.ParserResidualCreatesSourceAbsence → ⊥
genericParserResidualDoesNotCreateSourceAbsence =
  GenericIngestWeld.parserResidualDoesNotCreateSourceAbsence

genericParserResidualDoesNotCreatePropositionAbsence :
  GenericIngestWeld.ParserResidualCreatesPropositionAbsence → ⊥
genericParserResidualDoesNotCreatePropositionAbsence =
  GenericIngestWeld.parserResidualDoesNotCreatePropositionAbsence

genericParserResidualDoesNotCreateEventAbsence :
  GenericIngestWeld.ParserResidualCreatesEventAbsence → ⊥
genericParserResidualDoesNotCreateEventAbsence =
  GenericIngestWeld.parserResidualDoesNotCreateEventAbsence

genericIngestConcreteLongDocumentUsesCanonicalRevision :
  GenericIngestWeldRegression.fixtureRegionReallyUsesCanonicalRevision
  ≡ GenericIngestWeldRegression.fixtureRegionReallyUsesCanonicalRevision
genericIngestConcreteLongDocumentUsesCanonicalRevision = refl

genericIngestConcreteObservationUsesExactRegionSpan :
  GenericIngestWeldRegression.fixtureObservationReallyUsesRegionSpan
  ≡ GenericIngestWeldRegression.fixtureObservationReallyUsesRegionSpan
genericIngestConcreteObservationUsesExactRegionSpan = refl

------------------------------------------------------------------------
-- INGEST-1A durable long-document persistence remains non-semantic.
------------------------------------------------------------------------

longDocumentPersistenceDoesNotCreateSemanticAuthority :
  LongDocumentPersistence.PersistenceCreatesSemanticAuthority → ⊥
longDocumentPersistenceDoesNotCreateSemanticAuthority =
  LongDocumentPersistence.persistenceDoesNotCreateSemanticAuthority

longDocumentPersistenceDoesNotCreateReviewPayment :
  LongDocumentPersistence.PersistenceCreatesReviewPayment → ⊥
longDocumentPersistenceDoesNotCreateReviewPayment =
  LongDocumentPersistence.persistenceDoesNotCreateReviewPayment

longDocumentPersistenceDoesNotCreateClaimTruth :
  LongDocumentPersistence.PersistenceCreatesClaimTruth → ⊥
longDocumentPersistenceDoesNotCreateClaimTruth =
  LongDocumentPersistence.persistenceDoesNotCreateClaimTruth

longDocumentReloadPreservesPartition :
  LongDocumentPersistence.ReloadChangesRegionPartition → ⊥
longDocumentReloadPreservesPartition =
  LongDocumentPersistence.reloadDoesNotChangeRegionPartition

longDocumentConcreteReloadPreservesPartition :
  LongDocumentPersistenceRegression.fixtureReloadPreservesPartition
  ≡ LongDocumentPersistenceRegression.fixtureReloadPreservesPartition
longDocumentConcreteReloadPreservesPartition = refl

------------------------------------------------------------------------
-- SCALE-1 DB-native source/semantic compilation remains below admission.
------------------------------------------------------------------------

dbNativeFlatFilesAreNotRuntimeDatabase :
  DbNativeCorpus.FlatFileIsRuntimeDatabase → ⊥
dbNativeFlatFilesAreNotRuntimeDatabase =
  DbNativeCorpus.flatFileDoesNotBecomeRuntimeDatabase

dbNativeTsvIsNotRuntimeDatabase :
  DbNativeCorpus.TsvArtifactIsRuntimeDatabase → ⊥
dbNativeTsvIsNotRuntimeDatabase =
  DbNativeCorpus.tsvArtifactDoesNotBecomeRuntimeDatabase

dbNativeParserLeaseDoesNotCreateSourceAuthority :
  DbNativeCorpus.ParserLeaseCreatesSourceAuthority → ⊥
dbNativeParserLeaseDoesNotCreateSourceAuthority =
  DbNativeCorpus.parserLeaseDoesNotCreateSourceAuthority

dbNativeParserResidualDoesNotCreateSourceAbsence :
  DbNativeCorpus.ParserResidualCreatesSourceAbsence → ⊥
dbNativeParserResidualDoesNotCreateSourceAbsence =
  DbNativeCorpus.parserResidualDoesNotCreateSourceAbsence

dbNativePostgresDoesNotCreateGlobalTruth :
  DbNativeCorpus.PostgresCompilerStateCreatesGlobalTruth → ⊥
dbNativePostgresDoesNotCreateGlobalTruth =
  DbNativeCorpus.postgresCompilerStateDoesNotCreateGlobalTruth

dbNativeAutomaticExtractionDoesNotCreateAdmission :
  DbNativeCorpus.AutomaticExtractionCreatesAutomaticAdmission → ⊥
dbNativeAutomaticExtractionDoesNotCreateAdmission =
  DbNativeCorpus.automaticExtractionDoesNotCreateAutomaticAdmission

dbNativeFixtureAttemptsEverySemanticRegion :
  DbNativeCorpusRegression.fixtureHasNoUnattemptedSemanticRegions
  ≡ DbNativeCorpusRegression.fixtureHasNoUnattemptedSemanticRegions
dbNativeFixtureAttemptsEverySemanticRegion = refl

dbNativeContentDigestDoesNotDetermineRevisionIdentity :
  DbNativeCorpus.ContentDigestDeterminesSourceRevisionIdentity → ⊥
dbNativeContentDigestDoesNotDetermineRevisionIdentity =
  DbNativeCorpus.contentDigestDoesNotDetermineSourceRevisionIdentity

dbNativePersistedCandidateDoesNotCreateAdmission :
  DbNativeCorpus.PersistedCandidateCreatesSemanticAdmission → ⊥
dbNativePersistedCandidateDoesNotCreateAdmission =
  DbNativeCorpus.persistedCandidateDoesNotCreateSemanticAdmission

dbNativePersistedCandidateDoesNotCreateTruth :
  DbNativeCorpus.PersistedCandidateCreatesClaimTruth → ⊥
dbNativePersistedCandidateDoesNotCreateTruth =
  DbNativeCorpus.persistedCandidateDoesNotCreateClaimTruth

dbNativeFixtureCandidateReloadsWithoutAdmission :
  DbNativeCorpusRegression.fixtureCandidateReloadsWithoutAdmission
  ≡ DbNativeCorpusRegression.fixtureCandidateReloadsWithoutAdmission
dbNativeFixtureCandidateReloadsWithoutAdmission = refl


dbNativeReviewProjectionDoesNotCreateEventAssembly :
  DbNativeCorpus.ReviewQueueProjectionCreatesEventAssembly → ⊥
dbNativeReviewProjectionDoesNotCreateEventAssembly =
  DbNativeCorpus.reviewQueueProjectionDoesNotCreateEventAssembly

dbNativeReviewProjectionDoesNotCreatePropositionIdentity :
  DbNativeCorpus.ReviewQueueProjectionCreatesPropositionIdentity → ⊥
dbNativeReviewProjectionDoesNotCreatePropositionIdentity =
  DbNativeCorpus.reviewQueueProjectionDoesNotCreatePropositionIdentity

dbNativeReviewProjectionDoesNotCreateTruth :
  DbNativeCorpus.ReviewQueueProjectionCreatesClaimTruth → ⊥
dbNativeReviewProjectionDoesNotCreateTruth =
  DbNativeCorpus.reviewQueueProjectionDoesNotCreateClaimTruth

dbNativeFixtureReviewProjectionStaysBelowEventAssembly :
  DbNativeCorpusRegression.fixtureReviewProjectionDoesNotCreateEventAssembly
  ≡ DbNativeCorpusRegression.fixtureReviewProjectionDoesNotCreateEventAssembly
dbNativeFixtureReviewProjectionStaysBelowEventAssembly = refl


dbNativeGroupingReviewDoesNotPayClaimReview :
  DbNativeCorpus.GroupingReviewIsClaimReview → ⊥
dbNativeGroupingReviewDoesNotPayClaimReview =
  DbNativeCorpus.groupingReviewDoesNotPayClaimReview

dbNativeGroupingReviewDoesNotCreateClaimTruth :
  DbNativeCorpus.GroupingReviewCreatesClaimTruth → ⊥
dbNativeGroupingReviewDoesNotCreateClaimTruth =
  DbNativeCorpus.groupingReviewDoesNotCreateClaimTruth

dbNativeFixtureGroupingReviewLeavesClaimsUnreviewed :
  DbNativeCorpusRegression.fixtureGroupingReviewDoesNotPayClaimReview
  ≡ DbNativeCorpusRegression.fixtureGroupingReviewDoesNotPayClaimReview
dbNativeFixtureGroupingReviewLeavesClaimsUnreviewed = refl


dbNativeAutoObservationDoesNotCreateObservationIdentity :
  DbNativeCorpus.AutoObservationCreatesObservationIdentity → ⊥
dbNativeAutoObservationDoesNotCreateObservationIdentity =
  DbNativeCorpus.autoObservationDoesNotCreateObservationIdentity

dbNativeAutoObservationDoesNotCreateEventIdentity :
  DbNativeCorpus.AutoObservationCreatesEventIdentity → ⊥
dbNativeAutoObservationDoesNotCreateEventIdentity =
  DbNativeCorpus.autoObservationDoesNotCreateEventIdentity

dbNativeAutoProposalDoesNotCreateEventIdentity :
  DbNativeCorpus.AutoJoinProposalCreatesEventIdentity → ⊥
dbNativeAutoProposalDoesNotCreateEventIdentity =
  DbNativeCorpus.autoJoinProposalDoesNotCreateEventIdentity

dbNativeAutoProposalDoesNotCreateClaimTruth :
  DbNativeCorpus.AutoJoinProposalCreatesClaimTruth → ⊥
dbNativeAutoProposalDoesNotCreateClaimTruth =
  DbNativeCorpus.autoJoinProposalDoesNotCreateClaimTruth

dbNativeFixtureAutoProposalRemainsReviewGated :
  DbNativeCorpusRegression.fixtureAutoProposalRequiresReview
  ≡ DbNativeCorpusRegression.fixtureAutoProposalRequiresReview
dbNativeFixtureAutoProposalRemainsReviewGated = refl


------------------------------------------------------------------------
-- SCALE-1.P exact compiler-product reuse remains a physical optimisation.
------------------------------------------------------------------------

dbNativeExactReuseDoesNotCreateAdmission :
  DbNativeCorpus.ExactReuseCreatesSemanticAdmission → ⊥
dbNativeExactReuseDoesNotCreateAdmission =
  DbNativeCorpus.exactReuseDoesNotCreateSemanticAdmission

dbNativeExactReuseDoesNotCreateAuthority :
  DbNativeCorpus.ExactReuseCreatesSemanticAuthority → ⊥
dbNativeExactReuseDoesNotCreateAuthority =
  DbNativeCorpus.exactReuseDoesNotCreateSemanticAuthority

dbNativeExactReuseDoesNotCreateApplicability :
  DbNativeCorpus.ExactReuseCreatesApplicability → ⊥
dbNativeExactReuseDoesNotCreateApplicability =
  DbNativeCorpus.exactReuseDoesNotCreateApplicability

dbNativeExactReuseDoesNotCreateEntityIdentity :
  DbNativeCorpus.ExactReuseCreatesEntityIdentity → ⊥
dbNativeExactReuseDoesNotCreateEntityIdentity =
  DbNativeCorpus.exactReuseDoesNotCreateEntityIdentity

dbNativeExactReuseDoesNotCreatePropositionIdentity :
  DbNativeCorpus.ExactReuseCreatesPropositionIdentity → ⊥
dbNativeExactReuseDoesNotCreatePropositionIdentity =
  DbNativeCorpus.exactReuseDoesNotCreatePropositionIdentity

dbNativeExactReuseDoesNotCreateEventIdentity :
  DbNativeCorpus.ExactReuseCreatesEventIdentity → ⊥
dbNativeExactReuseDoesNotCreateEventIdentity =
  DbNativeCorpus.exactReuseDoesNotCreateEventIdentity

dbNativeExactReuseDoesNotCreateClaimTruth :
  DbNativeCorpus.ExactReuseCreatesClaimTruth → ⊥
dbNativeExactReuseDoesNotCreateClaimTruth =
  DbNativeCorpus.exactReuseDoesNotCreateClaimTruth

dbNativeFixtureExactReuseRequiresIdentity :
  DbNativeCorpusRegression.fixtureExactReuseRequiresMatchingIdentity
  ≡ DbNativeCorpusRegression.fixtureExactReuseRequiresMatchingIdentity
dbNativeFixtureExactReuseRequiresIdentity = refl

dbNativeFixtureExactReuseRequiresCompleteProduct :
  DbNativeCorpusRegression.fixtureExactReuseRequiresCompleteProduct
  ≡ DbNativeCorpusRegression.fixtureExactReuseRequiresCompleteProduct
dbNativeFixtureExactReuseRequiresCompleteProduct = refl

module DASHI.Cognition.PNF.SensibLawSelectiveLegalCompilerEverything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact as Routing
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawPdfActiveRequirementPlannerLiveExact as Pdf
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as ApplicabilityMeet
import DASHI.Cognition.PNF.SensibLawFullyPaidApplicabilityFixtureExact as PaidApplicability
import DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact as ViolationMeet
import DASHI.Cognition.PNF.SensibLawFullyPaidViolationPlannerExact as PaidViolation
import DASHI.Cognition.PNF.SensibLawLiabilityPrerequisiteMeetExact as LiabilityMeet
import DASHI.Cognition.PNF.SensibLawFullyPaidLiabilityPlannerExact as PaidLiability
import DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact as Evidence
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as Jurisdiction
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue
import DASHI.Cognition.PNF.SensibLawIssueBurdenStandardRemedyBidiExact as IssueBSR
import DASHI.Cognition.PNF.SensibLawAdjudicativeTemporalNonRetroactivityExact as Temporal

------------------------------------------------------------------------
-- EXISTING SELECTIVE COMPILER PATH.
------------------------------------------------------------------------

pdfReusesAttribution : Planner.action Pdf.attributionPlan ≡ Planner.reuseExisting
pdfReusesAttribution = refl
pdfReusesProposition : Planner.action Pdf.propositionPlan ≡ Planner.reuseExisting
pdfReusesProposition = refl
pdfReusesOccurrence : Planner.action Pdf.occurrencePlan ≡ Planner.reuseExisting
pdfReusesOccurrence = refl
pdfReusesDocumentContext : Planner.action Pdf.documentContextPlan ≡ Planner.reuseExisting
pdfReusesDocumentContext = refl
pdfInspectsEvidence : Planner.action Pdf.resolvedEvidencePlan ≡ Planner.inspectForEvidence
pdfInspectsEvidence = refl
pdfInspectsAuthority : Planner.action Pdf.legalSourceAuthorityPlan ≡ Planner.inspectForEvidence
pdfInspectsAuthority = refl
pdfInspectsScope : Planner.action Pdf.resolvedScopePlan ≡ Planner.inspectForEvidence
pdfInspectsScope = refl
pdfInspectsJurisdiction : Planner.action Pdf.resolvedJurisdictionPlan ≡ Planner.inspectForEvidence
pdfInspectsJurisdiction = refl

fullyPaidApplicabilityIsCandidate : Legal.resultingApplicability PaidApplicability.compiledApplicability ≡ Status.applicabilityCandidate
fullyPaidApplicabilityIsCandidate = refl
fullyPaidViolationIsCandidate : Legal.resultingViolation PaidViolation.compiledViolation ≡ Status.violationCandidate
fullyPaidViolationIsCandidate = refl
fullyPaidLiabilityIsCandidate : Legal.resultingLiability PaidLiability.compiledLiability ≡ Status.liabilityCandidate
fullyPaidLiabilityIsCandidate = refl
liabilityRetainsCandidateViolation : Legal.resultingViolation (Legal.violationReceipt PaidLiability.compiledLiability) ≡ Status.violationCandidate
liabilityRetainsCandidateViolation = refl

resolvedEvidenceHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalEvidenceResolutionProducer Demand.resolvedLegalEvidenceCoordinate
resolvedEvidenceHasDedicatedProducer = Routing.legalEvidencePopulatesResolvedEvidence
resolvedJurisdictionHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalJurisdictionProducer Demand.resolvedLegalJurisdictionCoordinate
resolvedJurisdictionHasDedicatedProducer = Routing.legalJurisdictionPopulatesResolvedJurisdiction
resolvedLegalRoleHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalRoleResolutionProducer Demand.legalRoleCoordinate
resolvedLegalRoleHasDedicatedProducer = Routing.legalRoleResolutionPopulatesLegalRole
legalSourceAuthorityHasDedicatedProducer : Routing.ProducerCanPopulate Cross.legalSourceAuthorityProducer Demand.legalSourceAuthorityCoordinate
legalSourceAuthorityHasDedicatedProducer = Routing.legalSourcePopulatesAuthority

mixedApplicabilityReceiptsBlocked : ApplicabilityMeet.MixedObjectReceiptsAuthorizeApplicabilityMeet → ⊥
mixedApplicabilityReceiptsBlocked = ApplicabilityMeet.mixedObjectReceiptsDoNotAuthorizeMeet
candidateViolationCannotAdmitLiability : LiabilityMeet.CandidateViolationAdmitsLiability → ⊥
candidateViolationCannotAdmitLiability = LiabilityMeet.candidateViolationDoesNotAdmitLiability
applicabilityDoesNotAutoViolate : ViolationMeet.ApplicabilityAutomaticallyProvesViolation → ⊥
applicabilityDoesNotAutoViolate = ViolationMeet.applicabilityDoesNotAutomaticallyProveViolation
liabilityDoesNotAutoSelectRemedy : LiabilityMeet.LiabilityAutomaticallySelectsRemedy → ⊥
liabilityDoesNotAutoSelectRemedy = LiabilityMeet.liabilityDoesNotAutomaticallySelectRemedy
parserEvidenceStillCannotPayResolvedLegalEvidence : Evidence.ParserEvidencePaysResolvedLegalEvidence → ⊥
parserEvidenceStillCannotPayResolvedLegalEvidence = Evidence.parserEvidenceDoesNotPayResolvedLegalEvidence
geographicMentionStillCannotResolveLegalJurisdiction : Jurisdiction.GeographicMentionIsResolvedLegalJurisdiction → ⊥
geographicMentionStillCannotResolveLegalJurisdiction = Jurisdiction.geographicMentionDoesNotResolveLegalJurisdiction
semanticAdmissionStillCannotBecomeLegalSourceAuthority : Authority.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
semanticAdmissionStillCannotBecomeLegalSourceAuthority = Authority.semanticAdmissionDoesNotBecomeLegalSourceAuthority

priorViolationSnapshotRetained : Bridge._∈_ PaidViolation.postViolationLegalStatus (Status.legalStatuses PaidLiability.postLiabilityState)
priorViolationSnapshotRetained = PaidLiability.priorViolationSnapshotRetained
priorApplicabilitySnapshotRetained : Bridge._∈_ PaidApplicability.fixtureLegalStatus (Status.legalStatuses PaidLiability.postLiabilityState)
priorApplicabilitySnapshotRetained = PaidLiability.priorApplicabilitySnapshotRetained

------------------------------------------------------------------------
-- ISSUE-INDEXED ADJUDICATIVE HYPERFABRIC.
-- The linear chain above is one valid compiled path, not universal topology.
------------------------------------------------------------------------

burdenMayCloseBeforeLiability :
  Issue.firstAdjudicativeResidual Issue.identifyBurdenQuery Issue.burdenCanCloseWithoutLiability
  ≡ Issue.adjudicativeClosed
burdenMayCloseBeforeLiability = refl

remedyMayStopAtIndependentSourceResidual :
  Issue.firstAdjudicativeResidual Issue.remedyEligibilityQuery Issue.candidateLiabilityButNoRemedySource
  ≡ Issue.remedySourceResidual
remedyMayStopAtIndependentSourceResidual = refl

liabilityDoesNotFixBurden : IssueBSR.LiabilityDeterminesIssueBurden → ⊥
liabilityDoesNotFixBurden = IssueBSR.liabilityDoesNotDetermineIssueBurden

liabilityDoesNotFixStandard : IssueBSR.LiabilityDeterminesIssueStandard → ⊥
liabilityDoesNotFixStandard = IssueBSR.liabilityDoesNotDetermineIssueStandard

candidateLiabilityCannotAdmitRemedy : IssueBSR.CandidateLiabilityAdmitsRemedyEligibility → ⊥
candidateLiabilityCannotAdmitRemedy = IssueBSR.candidateLiabilityDoesNotAdmitRemedy

oneLinearPipelineNotUniversal : Issue.OneFixedLinearPipelineFitsEveryLegalQuery → ⊥
oneLinearPipelineNotUniversal = Issue.oneLinearPipelineDoesNotFitEveryQuery

legalConclusionDoesNotBecomePhysicalAuthority : Issue.LegalConclusionAuthorisesPhysicalAction → ⊥
legalConclusionDoesNotBecomePhysicalAuthority = Issue.legalConclusionDoesNotAuthorisePhysicalAction

laterEvidenceDoesNotRetroactivelyPayEarlierBurden :
  Temporal.LaterEvidenceRetroactivelySatisfiesEarlierBurden → ⊥
laterEvidenceDoesNotRetroactivelyPayEarlierBurden = Temporal.laterEvidenceDoesNotRetroactivelySatisfyBurden

laterFindingDoesNotRetroactivelyPayEarlierStandard :
  Temporal.LaterFindingRetroactivelySatisfiesEarlierStandard → ⊥
laterFindingDoesNotRetroactivelyPayEarlierStandard = Temporal.laterFindingDoesNotRetroactivelySatisfyStandard

------------------------------------------------------------------------
-- Aggregate import is not a kernel receipt.
------------------------------------------------------------------------

data SelectiveLegalCompilerAggregateMeansKernelValidated : Set where
aggregateDoesNotClaimKernelValidation : SelectiveLegalCompilerAggregateMeansKernelValidated → ⊥
aggregateDoesNotClaimKernelValidation ()

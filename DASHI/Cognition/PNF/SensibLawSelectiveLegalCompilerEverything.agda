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

------------------------------------------------------------------------
-- FOCUSED SELECTIVE LEGAL COMPILER ROOT
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

fullyPaidApplicabilityIsCandidate :
  Legal.resultingApplicability PaidApplicability.compiledApplicability
  ≡ Status.applicabilityCandidate
fullyPaidApplicabilityIsCandidate = refl

fullyPaidViolationIsCandidate :
  Legal.resultingViolation PaidViolation.compiledViolation
  ≡ Status.violationCandidate
fullyPaidViolationIsCandidate = refl

fullyPaidLiabilityIsCandidate :
  Legal.resultingLiability PaidLiability.compiledLiability
  ≡ Status.liabilityCandidate
fullyPaidLiabilityIsCandidate = refl

liabilityRetainsCandidateViolation :
  Legal.resultingViolation (Legal.violationReceipt PaidLiability.compiledLiability)
  ≡ Status.violationCandidate
liabilityRetainsCandidateViolation = refl

------------------------------------------------------------------------
-- Producer ownership remains separated.
------------------------------------------------------------------------

resolvedEvidenceHasDedicatedProducer :
  Routing.ProducerCanPopulate
    Cross.legalEvidenceResolutionProducer Demand.resolvedLegalEvidenceCoordinate
resolvedEvidenceHasDedicatedProducer = Routing.legalEvidencePopulatesResolvedEvidence

resolvedJurisdictionHasDedicatedProducer :
  Routing.ProducerCanPopulate
    Cross.legalJurisdictionProducer Demand.resolvedLegalJurisdictionCoordinate
resolvedJurisdictionHasDedicatedProducer = Routing.legalJurisdictionPopulatesResolvedJurisdiction

resolvedLegalRoleHasDedicatedProducer :
  Routing.ProducerCanPopulate
    Cross.legalRoleResolutionProducer Demand.legalRoleCoordinate
resolvedLegalRoleHasDedicatedProducer = Routing.legalRoleResolutionPopulatesLegalRole

legalSourceAuthorityHasDedicatedProducer :
  Routing.ProducerCanPopulate
    Cross.legalSourceAuthorityProducer Demand.legalSourceAuthorityCoordinate
legalSourceAuthorityHasDedicatedProducer = Routing.legalSourcePopulatesAuthority

------------------------------------------------------------------------
-- Compiler-level hard boundaries.
------------------------------------------------------------------------

mixedApplicabilityReceiptsBlocked :
  ApplicabilityMeet.MixedObjectReceiptsAuthorizeApplicabilityMeet → ⊥
mixedApplicabilityReceiptsBlocked = ApplicabilityMeet.mixedObjectReceiptsDoNotAuthorizeMeet

candidateViolationCannotAdmitLiability :
  LiabilityMeet.CandidateViolationAdmitsLiability → ⊥
candidateViolationCannotAdmitLiability = LiabilityMeet.candidateViolationDoesNotAdmitLiability

applicabilityDoesNotAutoViolate :
  ViolationMeet.ApplicabilityAutomaticallyProvesViolation → ⊥
applicabilityDoesNotAutoViolate = ViolationMeet.applicabilityDoesNotAutomaticallyProveViolation

liabilityDoesNotAutoSelectRemedy :
  LiabilityMeet.LiabilityAutomaticallySelectsRemedy → ⊥
liabilityDoesNotAutoSelectRemedy = LiabilityMeet.liabilityDoesNotAutomaticallySelectRemedy

parserEvidenceStillCannotPayResolvedLegalEvidence :
  Evidence.ParserEvidencePaysResolvedLegalEvidence → ⊥
parserEvidenceStillCannotPayResolvedLegalEvidence = Evidence.parserEvidenceDoesNotPayResolvedLegalEvidence

geographicMentionStillCannotResolveLegalJurisdiction :
  Jurisdiction.GeographicMentionIsResolvedLegalJurisdiction → ⊥
geographicMentionStillCannotResolveLegalJurisdiction = Jurisdiction.geographicMentionDoesNotResolveLegalJurisdiction

semanticAdmissionStillCannotBecomeLegalSourceAuthority :
  Authority.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
semanticAdmissionStillCannotBecomeLegalSourceAuthority = Authority.semanticAdmissionDoesNotBecomeLegalSourceAuthority

------------------------------------------------------------------------
-- State refinement is additive: later status snapshots retain earlier ones.
------------------------------------------------------------------------

priorViolationSnapshotRetained :
  PaidViolation.postViolationLegalStatus Bridge.∈
    Status.legalStatuses PaidLiability.postLiabilityState
priorViolationSnapshotRetained = PaidLiability.priorViolationSnapshotRetained

priorApplicabilitySnapshotRetained :
  PaidApplicability.fixtureLegalStatus Bridge.∈
    Status.legalStatuses PaidLiability.postLiabilityState
priorApplicabilitySnapshotRetained = PaidLiability.priorApplicabilitySnapshotRetained

------------------------------------------------------------------------
-- Aggregate import is not a kernel receipt.
------------------------------------------------------------------------

data SelectiveLegalCompilerAggregateMeansKernelValidated : Set where

aggregateDoesNotClaimKernelValidation :
  SelectiveLegalCompilerAggregateMeansKernelValidated → ⊥
aggregateDoesNotClaimKernelValidation ()

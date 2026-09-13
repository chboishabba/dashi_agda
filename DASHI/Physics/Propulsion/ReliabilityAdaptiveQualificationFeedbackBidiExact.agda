{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.ReliabilityAdaptiveQualificationFeedbackBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Planning.CorkySoftOperationalPatternAtlasExact as Corky
import DASHI.Physics.Propulsion.QualifiedHotSectionManufacturingBidiExact as Qual
import DASHI.Physics.Propulsion.CorkySoftManufacturingMissionOperationsBidiExact as Ops
import DASHI.Physics.Propulsion.ReliabilityCapacityResourceDemandBidiExact as Capacity

------------------------------------------------------------------------
-- REALISED RELIABILITY/YIELD -> REVIEWED REVISION -> FUTURE CAPACITY
--
-- This owner closes the reverse direction of the reliability/capacity lane.
-- Historical observations and capacity states are append-only evidence.  A
-- realised anomaly may propose a process/inspection/qualification change, but
-- only an explicit reviewed approval creates a new revision.  The revised
-- policy/envelope may then parameterise a FUTURE capacity distribution; it does
-- not rewrite historical execution or manufacture counterfactual past yields.
------------------------------------------------------------------------

data FeedbackDomain : Set where
  aviationReliability : FeedbackDomain
  semiconductorYield : FeedbackDomain
  datacentreHardwareReliability : FeedbackDomain

record HistoricalCapacityObservation : Set where
  constructor historical-capacity-observation
  field
    domain : FeedbackDomain
    population : Capacity.PopulationIdentity
    reliability : Capacity.ReliabilityObservation
    capacity : Capacity.QualifiedAvailableCapacity
    timeWindow : String
    sameHistoricalPopulation : Bool
    sameHistoricalPopulationIsTrue : sameHistoricalPopulation ≡ true
    evidenceReference : String

open HistoricalCapacityObservation public

------------------------------------------------------------------------
-- Revision proposals are typed by target and bounded scope.
------------------------------------------------------------------------

data RevisionTarget : Set where
  manufacturingProcessWindow : RevisionTarget
  inspectionAcceptanceRule : RevisionTarget
  maintenanceInterval : RevisionTarget
  qualificationEnvelope : RevisionTarget
  supplierOrLotAdmissionRule : RevisionTarget
  serviceabilityRule : RevisionTarget

record RevisionProposal : Set where
  constructor revision-proposal
  field
    sourceObservation : HistoricalCapacityObservation
    target : RevisionTarget
    previousRevision : String
    proposedRevision : String
    proposedChange : String
    boundedScope : String
    boundedChange : Bool
    boundedChangeIsTrue : boundedChange ≡ true
    reviewRequired : Bool
    reviewRequiredIsTrue : reviewRequired ≡ true

open RevisionProposal public

data RevisionDecision : Set where
  rejectedRevision : RevisionDecision
  approvedRevision : RevisionDecision

record ReviewedRevision : Set where
  constructor reviewed-revision
  field
    proposal : RevisionProposal
    decision : RevisionDecision
    reviewer : String
    reviewEvidence : String
    effectiveFrom : String
    historicalEvidencePreserved : Bool
    historicalEvidencePreservedIsTrue : historicalEvidencePreserved ≡ true

open ReviewedRevision public

------------------------------------------------------------------------
-- Only approved revisions can become future producer inputs.
------------------------------------------------------------------------

record ApprovedRevision : Set where
  constructor approved-revision
  field
    reviewed : ReviewedRevision
    approved : Bool
    approvedIsTrue : approved ≡ true
    newRevisionIdentity : String

open ApprovedRevision public

record FutureCapacityModelInput : Set where
  constructor future-capacity-model-input
  field
    revision : ApprovedRevision
    futurePopulationReference : String
    futureWindow : String
    processOrQualificationReference : String
    modelReference : String
    historicalObservationUsedAsCalibration : Bool
    historicalObservationUsedAsCalibrationIsTrue :
      historicalObservationUsedAsCalibration ≡ true

open FutureCapacityModelInput public

------------------------------------------------------------------------
-- A future capacity projection is distinct from historical capacity and from
-- realised future execution.
------------------------------------------------------------------------

record FutureCapacityProjection : Set where
  constructor future-capacity-projection
  field
    input : FutureCapacityModelInput
    grossUnitsCode : Nat
    projectedQualifiedUnitsCode : Nat
    projectedAvailableUnitsCode : Nat
    uncertaintyReference : String
    projectionEvidence : String

open FutureCapacityProjection public

------------------------------------------------------------------------
-- Existing qualification/operations/CorkySoft anchors.
------------------------------------------------------------------------

qualificationBoundary : Qual.CanonicalQualificationBoundary
qualificationBoundary = Qual.canonicalQualificationBoundary

operationsBoundary : Ops.CorkySoftManufacturingMissionOperationsBoundary
operationsBoundary = Ops.canonicalCorkySoftManufacturingMissionOperationsBoundary

corkySoftBoundary : Corky.CorkySoftOperationalPatternBoundary
corkySoftBoundary = Corky.canonicalCorkySoftOperationalPatternBoundary

capacityBoundary : Capacity.ReliabilityCapacityResourceBoundary
capacityBoundary = Capacity.canonicalReliabilityCapacityResourceBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data HistoricalAnomalyRewritesPastQualificationPermission : Set where

data ProposalImpliesApprovedRevisionPermission : Set where

data ApprovedRevisionImpliesImprovedFutureYieldPermission : Set where

data HistoricalCapacityEqualsFutureProjectionPermission : Set where

data OneObservationImpliesPopulationFailureLawPermission : Set where

data ModelProjectionImpliesRealisedFutureCapacityPermission : Set where

data FinancialOrOperationalPressureRewritesAcceptanceCriteriaPermission : Set where

historicalAnomalyDoesNotRewritePastQualification :
  HistoricalAnomalyRewritesPastQualificationPermission → ⊥
historicalAnomalyDoesNotRewritePastQualification ()

proposalDoesNotEqualApproval :
  ProposalImpliesApprovedRevisionPermission → ⊥
proposalDoesNotEqualApproval ()

approvedRevisionDoesNotGuaranteeImprovedFutureYield :
  ApprovedRevisionImpliesImprovedFutureYieldPermission → ⊥
approvedRevisionDoesNotGuaranteeImprovedFutureYield ()

historicalCapacityDoesNotEqualFutureProjection :
  HistoricalCapacityEqualsFutureProjectionPermission → ⊥
historicalCapacityDoesNotEqualFutureProjection ()

oneObservationDoesNotCreatePopulationFailureLaw :
  OneObservationImpliesPopulationFailureLawPermission → ⊥
oneObservationDoesNotCreatePopulationFailureLaw ()

projectionDoesNotEqualRealisedFutureCapacity :
  ModelProjectionImpliesRealisedFutureCapacityPermission → ⊥
projectionDoesNotEqualRealisedFutureCapacity ()

operationalPressureDoesNotRewriteAcceptanceCriteria :
  FinancialOrOperationalPressureRewritesAcceptanceCriteriaPermission → ⊥
operationalPressureDoesNotRewriteAcceptanceCriteria ()

------------------------------------------------------------------------
-- Reverse acquisition frontier.
------------------------------------------------------------------------

data FeedbackReverseTarget : Set where
  acquireFailureYieldMaintenancePopulation : FeedbackReverseTarget
  acquireHistoricalCapacitySameWindow : FeedbackReverseTarget
  acquireRootCauseOrProcessAssociation : FeedbackReverseTarget
  acquireRevisionProposal : FeedbackReverseTarget
  acquireIndependentReview : FeedbackReverseTarget
  acquireApprovedEffectiveRevision : FeedbackReverseTarget
  acquireFutureCapacityModel : FeedbackReverseTarget
  acquireFutureRealisedCapacity : FeedbackReverseTarget
  acquirePostRevisionComparison : FeedbackReverseTarget

record FeedbackReverseObligation : Set where
  constructor feedback-reverse-obligation
  field
    target : FeedbackReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open FeedbackReverseObligation public

record ReliabilityAdaptiveFeedbackBoundary : Set where
  constructor reliability-adaptive-feedback-boundary
  field
    historyAppendOnly : Bool
    historyAppendOnlyIsTrue : historyAppendOnly ≡ true
    revisionRequiresReview : Bool
    revisionRequiresReviewIsTrue : revisionRequiresReview ≡ true
    futureProjectionDistinctFromHistory : Bool
    futureProjectionDistinctFromHistoryIsTrue :
      futureProjectionDistinctFromHistory ≡ true
    projectionDistinctFromRealisedFuture : Bool
    projectionDistinctFromRealisedFutureIsTrue :
      projectionDistinctFromRealisedFuture ≡ true
    operationalPressureCannotSilentlyRewriteQualification : Bool
    operationalPressureCannotSilentlyRewriteQualificationIsTrue :
      operationalPressureCannotSilentlyRewriteQualification ≡ true

canonicalReliabilityAdaptiveFeedbackBoundary :
  ReliabilityAdaptiveFeedbackBoundary
canonicalReliabilityAdaptiveFeedbackBoundary =
  reliability-adaptive-feedback-boundary
    true refl true refl true refl true refl true refl

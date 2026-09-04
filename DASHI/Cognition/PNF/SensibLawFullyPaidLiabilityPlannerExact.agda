module DASHI.Cognition.PNF.SensibLawFullyPaidLiabilityPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawFullyPaidApplicabilityFixtureExact as Paid
import DASHI.Cognition.PNF.SensibLawFullyPaidViolationPlannerExact as ViolationPaid
import DASHI.Cognition.PNF.SensibLawLiabilityPrerequisiteMeetExact as LiabilityMeet
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge

------------------------------------------------------------------------
-- Reuse the exact post-violation receipts; do not rebuild upstream semantics.
------------------------------------------------------------------------

liabilityPrerequisites :
  LiabilityMeet.LiabilityPrerequisiteBundle ViolationPaid.postViolationState
liabilityPrerequisites =
  LiabilityMeet.liabilityPrerequisiteBundle
    ViolationPaid.ownedViolation
    ViolationPaid.ownedLegalRole
    ViolationPaid.resolvedEvidence
    ViolationPaid.authorityReceipt
    ViolationPaid.jurisdictionReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    "post-violation same-object liability prerequisite bundle"

------------------------------------------------------------------------
-- The fixture violation is only candidate, so liability is forced to candidate.
------------------------------------------------------------------------

liabilityDecision : LiabilityMeet.LiabilityDecision liabilityPrerequisites
liabilityDecision =
  LiabilityMeet.liabilityDecision
    Status.liabilityCandidate
    LiabilityMeet.candidateViolationUse
    "actor:X"
    ("fixture documentary evidence" ∷ "fixture duty-bearer weld" ∷ [])
    "fixture liability decision policy"
    true refl

liabilityInput : LiabilityMeet.LiabilityMeetInput ViolationPaid.postViolationState
liabilityInput =
  LiabilityMeet.liabilityMeetInput
    liabilityPrerequisites
    Ontology.negligent
    refl
    liabilityDecision

compiledLiability : Legal.LiabilityReceipt
compiledLiability = LiabilityMeet.compileLiabilityMeet liabilityInput

compiledLiabilityIsCandidate :
  Legal.resultingLiability compiledLiability ≡ Status.liabilityCandidate
compiledLiabilityIsCandidate = refl

candidateViolationWasNotPromoted :
  Legal.resultingViolation (Legal.violationReceipt compiledLiability)
  ≡ Status.violationCandidate
candidateViolationWasNotPromoted = refl

------------------------------------------------------------------------
-- Append a liability snapshot; retain applicability and violation history.
------------------------------------------------------------------------

postLiabilityLegalStatus : Status.LegalStatusProduct
postLiabilityLegalStatus =
  Status.legalStatusProduct
    Status.legalSystemJurisdiction
    Status.legalAuthority
    Status.conditionUnresolved
    Status.applicabilityCandidate
    Status.violationCandidate
    Status.liabilityCandidate
    Status.burdenKindUnresolved
    Status.standardUnresolved
    Status.submission
    Status.normativeRelationUnresolved

postLiabilityState : Status.SemanticCommitmentState
postLiabilityState =
  Status.semanticCommitmentState
    (Status.sourceCandidate ViolationPaid.postViolationState)
    (Status.subjects ViolationPaid.postViolationState)
    (Status.events ViolationPaid.postViolationState)
    (Status.propositions ViolationPaid.postViolationState)
    (postLiabilityLegalStatus ∷ Status.legalStatuses ViolationPaid.postViolationState)
    (Status.candidateOnly ViolationPaid.postViolationState)
    (Status.governedAdmissionPresent ViolationPaid.postViolationState)

priorViolationSnapshotRetained :
  ViolationPaid.postViolationLegalStatus Bridge.∈ Status.legalStatuses postLiabilityState
priorViolationSnapshotRetained = Bridge.there Bridge.here

priorApplicabilitySnapshotRetained :
  Paid.fixtureLegalStatus Bridge.∈ Status.legalStatuses postLiabilityState
priorApplicabilitySnapshotRetained = Bridge.there (Bridge.there Bridge.here)

------------------------------------------------------------------------
-- Liability does not itself pay burden, standard, or remedy eligibility.
------------------------------------------------------------------------

data LiabilityCandidateAutomaticallyAdmitted : Set where
data LiabilityReceiptAutomaticallyCreatesBurden : Set where
data LiabilityReceiptAutomaticallySelectsStandard : Set where
data LiabilityReceiptAutomaticallyMakesRemedyEligible : Set where
data PostLiabilitySnapshotErasesViolationHistory : Set where

candidateLiabilityDoesNotAutoAdmit : LiabilityCandidateAutomaticallyAdmitted → ⊥
candidateLiabilityDoesNotAutoAdmit ()

liabilityDoesNotAutomaticallyCreateBurden : LiabilityReceiptAutomaticallyCreatesBurden → ⊥
liabilityDoesNotAutomaticallyCreateBurden ()

liabilityDoesNotAutomaticallySelectStandard : LiabilityReceiptAutomaticallySelectsStandard → ⊥
liabilityDoesNotAutomaticallySelectStandard ()

liabilityDoesNotAutomaticallyMakeRemedyEligible : LiabilityReceiptAutomaticallyMakesRemedyEligible → ⊥
liabilityDoesNotAutomaticallyMakeRemedyEligible ()

postLiabilityStateRetainsViolationHistory : PostLiabilitySnapshotErasesViolationHistory → ⊥
postLiabilityStateRetainsViolationHistory ()

record FullyPaidLiabilityPlannerBoundary : Set where
  constructor fully-paid-liability-planner-boundary
  field
    sameViolationReceiptReused : Bool
    sameLegalRoleReused : Bool
    sameEvidenceReused : Bool
    sameAuthorityReused : Bool
    sameJurisdictionReused : Bool
    exactWrongTypeCulpabilityUsed : Bool
    candidateViolationYieldsCandidateLiability : Bool
    candidateViolationMayAdmitLiability : Bool
    liabilitySnapshotAppended : Bool
    priorViolationSnapshotRetained : Bool
    priorApplicabilitySnapshotRetained : Bool
    liabilityAutoCreatesBurden : Bool
    liabilityAutoSelectsRemedy : Bool

canonicalFullyPaidLiabilityPlannerBoundary : FullyPaidLiabilityPlannerBoundary
canonicalFullyPaidLiabilityPlannerBoundary =
  fully-paid-liability-planner-boundary
    true true true true true true true false true true true false false
